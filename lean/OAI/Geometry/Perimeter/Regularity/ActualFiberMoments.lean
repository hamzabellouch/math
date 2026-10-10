import OAI.Geometry.Perimeter.Regularity.ActualFiberSecondMoment
import OAI.Geometry.Perimeter.Regularity.NormalFluxError
import OAI.Geometry.Perimeter.Regularity.ActualFiberFirstMoment

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem actual_fiber_first_moment_error (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {M a b δ R : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hab : a+δ < b) (hR : 0 < R)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+δ ≤ R)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| ≤ a)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    |(∫ x in Metric.ball 0 R, normalWindowTest v φ b 1 x ∂perimeterMeasure E) -
      (∫ y in tsupport φ, φ y*exactFiberHeight E v b y)| ≤
        (M*b/2)*orientedTilt E v (Metric.ball 0 R) := by
  rw [← actual_fiber_signed_first_moment hn hmin hv hφ hcφ ha hδ hab hR hKR hh hphase]
  have h := normal_flux_error_le_tilt hn hmin hv hR
    (normalWindowTest_measurable hφ b 1)
    (normalWindowTest_bound hM (by linarith : 0 ≤ b) 1)
  simpa only [pow_one,div_mul_eq_mul_div] using h

theorem actual_fiber_second_moment_error (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : ∀ y, 0 ≤ φ y)
    {M a b δ R : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hab : a+δ < b) (hR : 0 < R)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+δ ≤ R)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| ≤ a)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    |(∫ x in Metric.ball 0 R, normalWindowTest v φ b 2 x ∂perimeterMeasure E) -
      (∫ y in tsupport φ, φ y*(exactFiberHeight E v b y)^2)| ≤
        (9/2*b^2*M)*orientedTilt E v (Metric.ball 0 R) := by
  have hf := normal_flux_error_le_tilt hn hmin hv hR
    (normalWindowTest_measurable hφ b 2)
    (normalWindowTest_bound hM (by linarith : 0 ≤ b) 2)
  have hs := actual_fiber_signed_second_moment hn hmin hv hφ hcφ hpφ hM
    ha hδ hab hR hKR hh hphase
  dsimp only at hs
  have habs : |(∫ x in Metric.ball 0 R, normalWindowTest v φ b 2 x *
      inner ℝ (approximateNormal E x) v ∂perimeterMeasure E) -
      (∫ y in tsupport φ, φ y*(exactFiberHeight E v b y)^2)| ≤
      4*b^2*M*orientedTilt E v (Metric.ball 0 R) := by
    rw [abs_of_nonneg hs.1]; exact hs.2
  calc
    _ ≤ |(∫ x in Metric.ball 0 R, normalWindowTest v φ b 2 x ∂perimeterMeasure E) -
        (∫ x in Metric.ball 0 R, normalWindowTest v φ b 2 x *
          inner ℝ (approximateNormal E x) v ∂perimeterMeasure E)| +
      |(∫ x in Metric.ball 0 R, normalWindowTest v φ b 2 x *
          inner ℝ (approximateNormal E x) v ∂perimeterMeasure E) -
        (∫ y in tsupport φ, φ y*(exactFiberHeight E v b y)^2)| := abs_sub_le _ _ _
    _ ≤ (M*b^2/2)*orientedTilt E v (Metric.ball 0 R) +
        4*b^2*M*orientedTilt E v (Metric.ball 0 R) := add_le_add (by simpa only [div_mul_eq_mul_div] using hf) habs
    _ = _ := by ring

theorem normalized_second_moment_defect_tendsto_zero
    (A B a e : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, 0 < a i) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ i, |A i-B i| ≤ C*(a i)^2*e i) :
    Tendsto (fun i ↦ (A i-B i)/(a i)^2) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun i ↦ ?_) (by simpa using he.norm.const_mul C)
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (sq_pos_of_pos (ha i))]
  apply (div_le_iff₀ (sq_pos_of_pos (ha i))).mpr
  calc
    |A i-B i| ≤ C*(a i)^2*e i := hbound i
    _ ≤ C*(a i)^2*‖e i‖ :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg hC (sq_nonneg _))
    _ = C*‖e i‖*(a i)^2 := by ring

end RPISingularHarnack

end

end OAI
