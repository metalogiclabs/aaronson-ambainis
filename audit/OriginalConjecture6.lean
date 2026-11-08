import AaronsonAmbainis.Main

/-!
# Independent bridge to Aaronson–Ambainis Conjecture 6

This is a separate formulation of Conjecture 6 in Aaronson and Ambainis,
"The Need for Structure in Quantum Speedups" (arXiv:0911.0996v3), also
Conjecture 1.7 of the journal version.

The historical `(ε/d)^{O(1)}` is interpreted here as the existence of one
*uniform positive natural exponent* for all instances. Whether that is the
intended informal interpretation is a separate mathematical judgment.

The definitions below use Mathlib primitives, not PSI's `PrintedConjecture`.
The one-way bridge imports PSI's theorem only as its premise. This file does
not establish equivalence of informal formulations or the quantum reduction.

From the repository root, after setting up pinned Lean and Mathlib:

  lake build AaronsonAmbainis.Main
  lake env lean audit/OriginalConjecture6.lean

The proof body below was separately checked against the released source at
commit `2a6ceaef872ae993708950f951989134084b851a` in CI run
https://github.com/heathsanchez/test/actions/runs/42485073471 .
-/

namespace IndependentAAAudit

private noncomputable def cubeValue (N : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p

private noncomputable def cubeMean (N : ℕ) (p : MvPolynomial (Fin N) ℝ) : ℝ :=
  (∑ X : Fin N → Bool, cubeValue N p X) / 2 ^ N

private noncomputable def cubeVariance (N : ℕ) (p : MvPolynomial (Fin N) ℝ) : ℝ :=
  (∑ X : Fin N → Bool, (cubeValue N p X - cubeMean N p) ^ 2) / 2 ^ N

private noncomputable def cubeInfluence (N : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (i : Fin N) : ℝ :=
  (∑ X : Fin N → Bool,
    (cubeValue N p X - cubeValue N p (Function.update X i (!X i))) ^ 2) / 2 ^ N

/-- Original exact-degree premise; `O(1)` means an existential uniform positive exponent.
    No PSI-defined proposition occurs in the specification. -/
def OriginalConjecture6 : Prop :=
  ∃ k : ℕ, 0 < k ∧
    ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree = d →
      (∀ X : Fin N → Bool, 0 ≤ cubeValue N p X ∧ cubeValue N p X ≤ 1) →
      ∀ ε : ℝ, 0 < ε → cubeVariance N p ≥ ε →
        ∃ i : Fin N, cubeInfluence N p i ≥ (ε / (d : ℝ)) ^ k

/-- PSI's exponent `7` supplies a uniform historical exponent; exact degree
    implies the at-most-degree premise. -/
theorem printed_implies_original
    (h : AaronsonAmbainis.PrintedConjecture) : OriginalConjecture6 := by
  refine ⟨7, by norm_num, ?_⟩
  intro N d p hDegree hBound ε hε hVar
  have hBound' :
      ∀ X : Fin N → Bool,
        0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
          MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1 := by
    simpa only [cubeValue] using hBound
  have hVar' :
      (∑ X : Fin N → Bool,
        (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
          - (∑ Y : Fin N → Bool,
              MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p) / 2 ^ N) ^ 2)
        / 2 ^ N ≥ ε := by
    simpa only [cubeVariance, cubeMean, cubeValue] using hVar
  obtain ⟨i, hi⟩ := h N d p (le_of_eq hDegree) hBound' ε hε hVar'
  refine ⟨i, ?_⟩
  simpa only [cubeInfluence, cubeValue] using hi

/-- A consumer of the original-form statement, without assuming the PSI theorem. -/
theorem historical_conjecture : OriginalConjecture6 :=
  printed_implies_original AaronsonAmbainis.aaronson_ambainis

end IndependentAAAudit

#print axioms IndependentAAAudit.historical_conjecture
