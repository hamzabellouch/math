import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # The exact weak flux of a forward/backward heat product

Two weak Laplacians tested against actual bounded Sobolev products give
the antisymmetric flux identity. All terms remain in the original measure.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weakLaplacian_bounded_product_test (u v w : SobolevSpace μ hQ)
    (d : Lp ℝ 2 μ) (hd : IsWeakLaplacian μ hQ u d) (B C : ℝ≥0)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ v x| ≤ B)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C) :
    (∫ x, SobolevSpace.toLp μ hQ v x * localGamma μ hQ u w x ∂μ) +
      (∫ x, SobolevSpace.toLp μ hQ w x * localGamma μ hQ u v x ∂μ) =
      -(∫ x, SobolevSpace.toLp μ hQ w x * (d x * SobolevSpace.toLp μ hQ v x) ∂μ) := by
  have hi₁ := (localGamma_memL1 μ hQ u w).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ v)) (by simpa only [Real.norm_eq_abs] using hv)
  have hi₂ := (localGamma_memL1 μ hQ u v).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ w)) (by simpa only [Real.norm_eq_abs] using hw)
  have htest := hd (SobolevSpace.product μ hQ v w B C)
  have hl : energyForm μ hQ u (SobolevSpace.product μ hQ v w B C) =
      (∫ x, SobolevSpace.toLp μ hQ v x * localGamma μ hQ u w x ∂μ) +
      (∫ x, SobolevSpace.toLp μ hQ w x * localGamma μ hQ u v x ∂μ) := by
    rw [← integral_localGamma_eq_energyForm,← integral_add hi₁ hi₂]
    exact integral_congr_ae (localGamma_product_right μ hQ u v w B C hv hw)
  have hr : inner ℝ d (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ v w B C)) =
      ∫ x, SobolevSpace.toLp μ hQ w x * (d x * SobolevSpace.toLp μ hQ v x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ v w B C hv hw] with x hx
    simp only [Real.inner_apply,hx]
    ring
  rwa [hl,hr] at htest

theorem weakLaplacian_product_flux (u v w : SobolevSpace μ hQ) (d e : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d) (he : IsWeakLaplacian μ hQ v e)
    (A B C : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ v x| ≤ B)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C) :
    (∫ x, SobolevSpace.toLp μ hQ w x *
      (d x * SobolevSpace.toLp μ hQ v x - SobolevSpace.toLp μ hQ u x * e x) ∂μ) =
      ∫ x, SobolevSpace.toLp μ hQ u x * localGamma μ hQ v w x -
        SobolevSpace.toLp μ hQ v x * localGamma μ hQ u w x ∂μ := by
  let U := SobolevSpace.toLp μ hQ u
  let V := SobolevSpace.toLp μ hQ v
  let W := SobolevSpace.toLp μ hQ w
  have hi₁ := ((Lp.memLp d).integrable_mul (Lp.memLp V)).bdd_mul
    (Lp.aestronglyMeasurable W) (by simpa only [Real.norm_eq_abs] using hw)
  have hi₂ := ((Lp.memLp U).integrable_mul (Lp.memLp e)).bdd_mul
    (Lp.aestronglyMeasurable W) (by simpa only [Real.norm_eq_abs] using hw)
  change Integrable (fun x => W x * (d x * V x)) μ at hi₁
  change Integrable (fun x => W x * (U x * e x)) μ at hi₂
  have hj₁ := (localGamma_memL1 μ hQ v w).bdd_mul
    (Lp.aestronglyMeasurable U) (by simpa only [Real.norm_eq_abs] using hu)
  have hj₂ := (localGamma_memL1 μ hQ u w).bdd_mul
    (Lp.aestronglyMeasurable V) (by simpa only [Real.norm_eq_abs] using hv)
  have h₁ := weakLaplacian_bounded_product_test μ hQ u v w d hd B C hv hw
  have h₂ := weakLaplacian_bounded_product_test μ hQ v u w e he A C hu hw
  have hsym : (∫ x, W x * localGamma μ hQ v u x ∂μ) =
      ∫ x, W x * localGamma μ hQ u v x ∂μ := by
    apply integral_congr_ae
    filter_upwards [localGamma_comm μ hQ v u] with x hx
    rw [hx]
  have hecomm : (∫ x, W x * (e x * U x) ∂μ) = ∫ x, W x * (U x * e x) ∂μ := by
    simp_rw [mul_comm (e _) (U _)]
  change _ + (∫ x, W x * localGamma μ hQ v u x ∂μ) =
    -(∫ x, W x * (e x * U x) ∂μ) at h₂
  rw [hsym,hecomm] at h₂
  change (∫ x, W x * (d x * V x - U x * e x) ∂μ) = _
  simp_rw [mul_sub]
  rw [integral_sub hi₁ hi₂,integral_sub hj₁ hj₂]
  linarith only [h₁,h₂]

end RegularPointCoordinates

end

end OAI
