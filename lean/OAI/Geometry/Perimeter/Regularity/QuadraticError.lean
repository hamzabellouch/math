import OAI.Geometry.Perimeter.Regularity.ActualFiberMoments
import OAI.Geometry.Perimeter.Regularity.ActualFiberZerothMoment
import OAI.Geometry.Perimeter.Regularity.QuadraticMoment

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem actual_fiber_quadratic_error (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {φ w : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : ∀ y, 0≤φ y)
    (hw : Continuous w) {M₂ M₁ M₀ a δ R : ℝ}
    (hM₂ : ∀ y, ‖φ y‖≤M₂) (hM₁ : ∀ y, ‖φ y*w y‖≤M₁)
    (hM₀ : ∀ y, ‖φ y*(w y)^2‖≤M₀)
    (ha : 0<a) (hδ : 0<δ) (hab : a+δ<2*a) (hR : 0<R)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+2*a+δ≤R)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x|≤a)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x∈E ↔ inner ℝ v x<0)) :
    |(∫ x in Metric.ball 0 R, normalWindowQuadratic v φ w a (2*a) x ∂perimeterMeasure E)-
      (∫ y, φ y*(exactFiberHeight E v (2*a) y/a-w y)^2)| ≤
        (18*M₂+2*M₁+M₀/2)*orientedTilt E v (Metric.ball 0 R) := by
  have h2 := actual_fiber_second_moment_error hn hmin hv hφ hcφ hpφ hM₂
    ha.le hδ hab hR hKR hh hphase
  have h1 := actual_fiber_first_moment_error hn hmin hv (hφ.mul hw) hcφ.mul_right hM₁
    ha.le hδ hab hR (fun y hy ↦ hKR y (tsupport_mul_subset_left hy)) hh hphase
  have h0 := actual_fiber_zeroth_moment_error hn hmin hv (hφ.mul (hw.pow 2)) hcφ.mul_right hM₀
    ha.le hδ hab hR (fun y hy ↦ hKR y (tsupport_mul_subset_left hy)) hh hphase
  rw [setIntegral_tsupport_mul] at h2 h1
  change |(∫ x in Metric.ball 0 R, normalWindowTest v (fun y ↦ φ y*(w y)^2) (2*a) 0 x ∂perimeterMeasure E)-
    (∫ y in tsupport (fun y ↦ φ y*(w y)^2), φ y*(w y)^2)| ≤ _ at h0
  have hz : (∫ y in tsupport (fun y ↦ φ y*(w y)^2), φ y*(w y)^2) = ∫ y, φ y*(w y)^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    exact Function.notMem_support.mp (fun hh ↦ hy (subset_closure hh))
  rw [hz] at h0
  rw [normalWindowQuadratic_integral_expand hmin v hφ hcφ hw (by positivity) hR,
    exactFiberQuadratic_integral_expand hmin.1 v hφ hcφ hw (by positivity)]
  have htri (A₂ A₁ A₀ B₂ B₁ B₀ : ℝ) :
      |((a⁻¹)^2*A₂-(2/a)*A₁+A₀)-((a⁻¹)^2*B₂-(2/a)*B₁+B₀)| ≤
        (a⁻¹)^2*|A₂-B₂|+(2/a)*|A₁-B₁|+|A₀-B₀| := by
    calc
      _ = |((a⁻¹)^2*(A₂-B₂)-(2/a)*(A₁-B₁))+(A₀-B₀)| := by congr 1; ring
      _ ≤ |(a⁻¹)^2*(A₂-B₂)-(2/a)*(A₁-B₁)|+|A₀-B₀| := abs_add_le _ _
      _ ≤ (|(a⁻¹)^2*(A₂-B₂)|+|(2/a)*(A₁-B₁)|)+|A₀-B₀| :=
        add_le_add (abs_sub _ _) le_rfl
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_pos (by positivity : 0<2/a)]
  refine (htri _ _ _ _ _ _).trans ?_
  have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h2 (sq_nonneg (a⁻¹)))
    (mul_le_mul_of_nonneg_left h1 (by positivity : 0≤2/a))) h0
  convert h using 1
  try rfl
  field_simp
  ring

end RPISingularHarnack

end

end OAI
