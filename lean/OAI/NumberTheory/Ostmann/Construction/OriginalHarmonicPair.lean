import OAI.NumberTheory.Ostmann.Construction.TwoCoordinatePrior
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # The two-prime estimate inside the original role-dependent harmonic law -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_restrict_sum (P Q : Finset ℕ) (hQP : Q ⊆ P) (F : ℕ → ℂ) :
    (∑ p : P, (primeSubsetPrior P Q p : ℂ) * F p) =
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * F q := by
  rw [primeSubsetPrior_mean P Q hQP F, primeSubsetPrior_mean Q Q (by rfl) F]

theorem twoCoordinateAssignment_map {V A B : Type*} (a b : V) (hab : a ≠ b)
    (f : A → B) (outside : OtherVertices a b → A) (q p : A) :
    (fun v => f (twoCoordinateAssignment a b hab outside q p v)) =
      twoCoordinateAssignment a b hab (fun v => f (outside v)) (f q) (f p) := by
  funext v
  unfold twoCoordinateAssignment
  cases (twoVertexEquiv a b hab).symm v with
  | inl t => cases t <;> rfl
  | inr v => rfl

/-- A uniform long/short-prime estimate is inserted in the complete original
expectation. The remaining coordinates retain their individual role priors. -/
theorem original_harmonic_pair_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) (P : Finset ℕ) (Q : V → Finset ℕ)
    (hQP : ∀ v, Q v ⊆ P) (hQmass : ∀ v, (∑ q ∈ Q v, (q : ℝ)⁻¹) ≠ 0)
    (F : (V → ℕ) → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsection : ∀ outside : OtherVertices a b → P,
      ‖∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        ∑ q : Q a, (primeSubsetPrior (Q a) (Q a) q : ℂ) *
          F (twoCoordinateAssignment a b hab (fun v => (outside v : ℕ)) (q : ℕ) (p : ℕ))‖ ≤ δ) :
    ‖∑ x : V → P, ((∏ v, primeSubsetPrior P (Q v) (x v) : ℝ) : ℂ) *
      F (fun v => (x v : ℕ))‖ ≤ δ := by
  apply original_prior_twoCoordinate_bound a b hab (fun v => primeSubsetPrior P (Q v))
    (fun v p => primeSubsetPrior_nonneg P (Q v) p)
    (fun v => (primeSubsetPrior_mass P (Q v) (hQP v) (hQmass v)).le)
    (fun x => F (fun v => (x v : ℕ))) δ hδ
  intro outside
  simp_rw [twoCoordinateAssignment_map]
  let outside' : OtherVertices a b → ℕ := fun v => (outside v : ℕ)
  have hp (q : ℕ) :
      (∑ p : P, (primeSubsetPrior P (Q b) p : ℂ) *
        F (twoCoordinateAssignment a b hab outside' q (p : ℕ))) =
      ∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        F (twoCoordinateAssignment a b hab outside' q (p : ℕ)) :=
    primeSubsetPrior_restrict_sum P (Q b) (hQP b)
      (fun p : ℕ => F (twoCoordinateAssignment a b hab outside' q p))
  change ‖∑ q : P, (primeSubsetPrior P (Q a) q : ℂ) *
    ∑ p : P, (primeSubsetPrior P (Q b) p : ℂ) *
      F (twoCoordinateAssignment a b hab outside' (q : ℕ) (p : ℕ))‖ ≤ δ
  simp_rw [hp]
  rw [primeSubsetPrior_restrict_sum P (Q a) (hQP a)
    (fun q : ℕ => ∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
      F (twoCoordinateAssignment a b hab outside' q (p : ℕ)))]
  have he : (∑ q : Q a, (primeSubsetPrior (Q a) (Q a) q : ℂ) *
      ∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        F (twoCoordinateAssignment a b hab outside' (q : ℕ) (p : ℕ))) =
      ∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        ∑ q : Q a, (primeSubsetPrior (Q a) (Q a) q : ℂ) *
          F (twoCoordinateAssignment a b hab outside' (q : ℕ) (p : ℕ)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he]
  exact hsection outside

end Ostmann

end OAI
