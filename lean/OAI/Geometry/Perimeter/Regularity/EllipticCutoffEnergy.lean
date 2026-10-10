import OAI.Geometry.Perimeter.Regularity.EllipticCaccioppoli
import OAI.Geometry.Perimeter.Regularity.EllipticScaleStep

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem cutoff_energy_bound {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} (hA : Continuous A) (hf : ContDiff ℝ 1 f)
    (hF : Continuous F) {p : Euc n} {r : ℝ} (h : WeakLinearEquation A f F (Metric.ball p r))
    (hnear : ∀ x∈Metric.ball p r, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖≤1/2)
    {χ : Euc n → ℝ} (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Metric.ball p r) {B N : ℝ}
    (hb : ∀ x, |f x|≤B) (hN : ∀ x, ‖F x‖≤N) :
    (∫ x, (χ x)^2*‖gradient f x‖^2) ≤
      256*(B^2*(∫ x, ‖gradient χ x‖^2)+N^2*(∫ x, (χ x)^2)) := by
  have hi₁ : Integrable (fun x ↦ ‖gradient χ x‖^2) volume := by
    simpa only [one_pow,one_mul] using square_compact_field_integrable
      (continuous_const : Continuous (fun _ : Euc n ↦ (1:ℝ))) (gradient_continuous_C1 hχ)
      (gradient_hasCompactSupport hcχ)
  have hi₂ : Integrable (fun x ↦ (χ x)^2) volume := by
    apply (hχ.continuous.pow 2).integrable_of_hasCompactSupport
    apply hcχ.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    exact fun hz ↦ hx (by simp [hz])
  have h1 : (∫ x, (f x)^2*‖gradient χ x‖^2)≤B^2*(∫ x, ‖gradient χ x‖^2) := by
    rw [←integral_const_mul]
    apply integral_mono (square_compact_field_integrable hf.continuous (gradient_continuous_C1 hχ)
      (gradient_hasCompactSupport hcχ)) (hi₁.const_mul _)
    intro x
    exact mul_le_mul_of_nonneg_right (by nlinarith [hb x,sq_abs (f x),abs_nonneg (f x)]) (sq_nonneg _)
  have h2 : (∫ x, (χ x)^2*‖F x‖^2)≤N^2*(∫ x, (χ x)^2) := by
    rw [←integral_const_mul]
    apply integral_mono (square_weight_integrable hχ.continuous hcχ hF) (hi₂.const_mul _)
    intro x
    have ht := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg (F x)) (hN x) 2) (sq_nonneg (χ x))
    simpa only [mul_comm] using ht
  exact (h.caccioppoli hA hf hF hnear hχ hcχ hsχ).trans (by linarith)

 theorem scaled_energy_le_cutoff {f χ : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ) {p : Euc n} {r : ℝ} (hr : 0<r)
    (hone : ∀ x∈Metric.ball p r, χ x=1) :
    scaledGradientEnergy f p r 0≤r^(-(n:ℤ))*(∫ x, (χ x)^2*‖gradient f x‖^2) := by
  have hi := square_weight_integrable hχ.continuous hcχ (gradient_continuous_C1 hf)
  have he : gradientEnergy f p r 0=(∫ x in Metric.ball p r, (χ x)^2*‖gradient f x‖^2) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    simp only [hone x hx,one_pow,one_mul,sub_zero]
  have hb : gradientEnergy f p r 0≤∫ x, (χ x)^2*‖gradient f x‖^2 := by
    rw [he]
    exact setIntegral_le_integral hi (ae_of_all _ (fun x ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0≤(r^n)⁻¹)
  simpa only [scaledGradientEnergy,zpow_neg,zpow_natCast] using hh

end RPISingularHarnack

end

end OAI
