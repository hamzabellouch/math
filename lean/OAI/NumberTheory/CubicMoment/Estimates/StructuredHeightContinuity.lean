import OAI.NumberTheory.CubicMoment.Estimates.StructuredHeightMass

namespace OAI

/-! Continuity and boundedness of the actual finite height mass. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullStructuredHeightMass_nonneg (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (t : ℝ) :
    0 ≤ fullStructuredHeightMass R H v e ℓ u W X t :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma continuous_fullStructuredHeightMass (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    Continuous (fullStructuredHeightMass R H v e ℓ u W X) := by
  exact continuous_finsetSum H (fun h _ =>
    ((continuous_fullStructuredAngularSum R h v e ℓ u W X).norm).pow 2)

lemma fullStructuredHeightMass_bounded (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, fullStructuredHeightMass R H v e ℓ u W X t ≤ B := by
  let A := fun h : Eisenstein => ∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
    ‖fullStructuredCoefficient R h v e W X z*theta ℓ z‖
  refine ⟨∑ h ∈ H, (A h)^2,Finset.sum_nonneg (fun _ _ => sq_nonneg _),?_⟩
  intro t
  apply Finset.sum_le_sum
  intro h _
  apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
  rw [fullStructuredAngularSum_eq]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro z _
  rw [norm_mul,mellinPhase_norm,mul_one]

end CubicFirstMoment

end

end OAI
