import OAI.Geometry.Perimeter.Regularity.GeoComposition
import OAI.Geometry.Perimeter.Regularity.NormalCoordinates

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ContDiff
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap

 theorem halfspace_horizontal_integral_unit {n : ℕ} {v w : Euc n}
    (hw : ‖w‖ = 1) (hvw : inner ℝ w v = 0)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x in {y | inner ℝ y v < 0}, fderiv ℝ φ x w) = 0 := by
  let H : Set (Euc n) := {y | inner ℝ y v < 0}
  have hHm : MeasurableSet H :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  have hi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hc
  have hdi : Integrable (fun x ↦ fderiv ℝ φ x w) volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ w)
  rw [← integral_indicator hHm]
  rw [integral_normalCoordinates w hw _ (hdi.indicator hHm)]
  have hm := normalCoordinates_measurePreserving w hw
  have hia := ((hm.integrable_comp hi.aestronglyMeasurable).mpr hi).prod_right_ae
  have hdia := ((hm.integrable_comp hdi.aestronglyMeasurable).mpr hdi).prod_right_ae
  apply integral_eq_zero_of_ae
  filter_upwards [hia,hdia] with y hy hdy
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ ↦ φ ((y:Euc n)+t•w))
      (fderiv ℝ φ ((y:Euc n)+s•w) w) s := by
    simpa only [Function.comp_def,id_eq,one_smul] using
      ((hφ.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt s
        (HasDerivAt.const_add (y:Euc n) ((hasDerivAt_id s).smul_const w))
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd hdy hy
  by_cases hyH : inner ℝ (y:Euc n) v < 0
  · simpa [H,Set.indicator,inner_add_left,real_inner_smul_left,hvw,hyH] using hz
  · simp [H,Set.indicator,inner_add_left,real_inner_smul_left,hvw,hyH]

 theorem halfspace_horizontal_integral {n : ℕ} {v w : Euc n}
    (hvw : inner ℝ v w = 0)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x in {y | inner ℝ y v < 0}, fderiv ℝ φ x w) = 0 := by
  by_cases hw : w=0
  · simp [hw]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u : Euc n := ‖w‖⁻¹ • w
  have hu : ‖u‖=1 := by simp [u,norm_smul,hn.ne']
  have huv : inner ℝ u v = 0 := by
    have hvw' : inner ℝ w v=0 := by rw [real_inner_comm]; exact hvw
    simp only [u,real_inner_smul_left,hvw',mul_zero]
  have he : w = ‖w‖ • u := by simp [u,smul_smul,hn.ne']
  have hh := halfspace_horizontal_integral_unit hu huv hφ hc
  conv_lhs => arg 2; ext x; rw [he,map_smul]
  simp only [smul_eq_mul]
  rw [integral_const_mul,hh,mul_zero]

end RPISingularHarnack

end

end OAI
