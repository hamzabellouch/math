import OAI.Geometry.Perimeter.Regularity.EllipticLocality
import OAI.Geometry.Perimeter.Regularity.NormalCoordinates

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary
variable {n m : ℕ}

def planeFiber (v : Euc n) (f : Euc n → ℝ) (y : normalPlane v) : ℝ :=
  ∫ s : ℝ, f ((y:Euc n)+s•v)

theorem planeFiber_measurable {f : Euc n → ℝ} (hf : Measurable f) (v : Euc n) :
    Measurable (planeFiber v f) := by
  have h : Measurable (fun p : normalPlane v × ℝ ↦ f ((p.1:Euc n)+p.2•v)) :=
    hf.comp ((continuous_subtype_val.comp continuous_fst).add
      (continuous_snd.smul continuous_const)).measurable
  exact h.stronglyMeasurable.integral_prod_right.measurable

theorem planeFiber_integrable {f : Euc n → ℝ} (hf : Integrable f volume)
    {v : Euc n} (hv : ‖v‖=1) : Integrable (planeFiber v f) volume := by
  have hi := ((normalCoordinates_measurePreserving v hv).integrable_comp
    hf.aestronglyMeasurable).mpr hf
  exact hi.integral_prod_left

theorem planeFiber_lintegral_le {f : Euc n → ℝ} (hf : Measurable f)
    {v : Euc n} (hv : ‖v‖=1) :
    (∫⁻ y : normalPlane v, ‖planeFiber v f y‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ := by
  rw [lintegral_normalCoordinates v hv _ hf.enorm]
  exact lintegral_mono (fun _ ↦ enorm_integral_le_lintegral_enorm _)

theorem planeFiber_translation_le {f : Euc n → ℝ} (hm : Measurable f)
    (hf : Integrable f volume) {v : Euc n} (hv : ‖v‖=1) (w : normalPlane v) :
    (∫⁻ y : normalPlane v, ‖planeFiber v f (y+w)-planeFiber v f y‖ₑ) ≤
      ∫⁻ x, ‖f (x+(w:Euc n))-f x‖ₑ := by
  have hi := ((normalCoordinates_measurePreserving v hv).integrable_comp
    hf.aestronglyMeasurable).mpr hf
  have hit : Integrable (fun x ↦ f (x+(w:Euc n))) volume := hf.comp_add_right _
  have hit' := ((normalCoordinates_measurePreserving v hv).integrable_comp
    hit.aestronglyMeasurable).mpr hit
  calc
    _ = ∫⁻ y : normalPlane v, ‖planeFiber v (fun x ↦ f (x+(w:Euc n))-f x) y‖ₑ := by
      apply lintegral_congr_ae
      filter_upwards [hi.prod_right_ae,hit'.prod_right_ae] with y hy hyt
      unfold planeFiber
      have he : (fun s : ℝ ↦ f (((y+w:normalPlane v):Euc n)+s•v)) =
          (fun s : ℝ ↦ f ((y:Euc n)+s•v+(w:Euc n))) := by
        funext s; congr 1; change (y:Euc n)+(w:Euc n)+s•v=(y:Euc n)+s•v+(w:Euc n); abel
      rw [he]
      dsimp only
      change Integrable (fun s : ℝ ↦ f ((y:Euc n)+s•v)) volume at hy
      change Integrable (fun s : ℝ ↦ f ((y:Euc n)+s•v+(w:Euc n))) volume at hyt
      rw [integral_sub hyt hy]
    _ ≤ _ := planeFiber_lintegral_le ((hm.comp (measurable_id.add measurable_const)).sub hm) hv

def chartFiber (v : Euc n) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    (a : ℝ) (f : Euc n → ℝ) (y : Euc m) : ℝ := a⁻¹*planeFiber v f (e y)

theorem chartFiber_measurable {f : Euc n → ℝ} (hf : Measurable f)
    (v : Euc n) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (a : ℝ) :
    Measurable (chartFiber v e a f) :=
  measurable_const.mul ((planeFiber_measurable hf v).comp e.continuous.measurable)

theorem chartFiber_integrable {f : Euc n → ℝ} (hf : Integrable f volume)
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (a : ℝ) :
    Integrable (chartFiber v e a f) volume := by
  have hi := planeFiber_integrable hf hv
  exact ((e.measurePreserving.integrable_comp hi.aestronglyMeasurable).mpr hi).const_mul _

theorem chartFiber_lintegral_le {f : Euc n → ℝ} (hf : Measurable f)
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (a : ℝ) :
    (∫⁻ y, ‖chartFiber v e a f y‖ₑ) ≤ ENNReal.ofReal |a⁻¹| * ∫⁻ x, ‖f x‖ₑ := by
  simp only [chartFiber,enorm_mul]
  rw [Real.enorm_eq_ofReal_abs (a⁻¹)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    e.measurePreserving.lintegral_comp ((planeFiber_measurable hf v).enorm)]
  exact mul_le_mul le_rfl (planeFiber_lintegral_le hf hv) zero_le zero_le

theorem chartFiber_translation_le {f : Euc n → ℝ} (hm : Measurable f)
    (hf : Integrable f volume) {v : Euc n} (hv : ‖v‖=1)
    (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (a : ℝ) (w : Euc m) :
    (∫⁻ y, ‖chartFiber v e a f (y+w)-chartFiber v e a f y‖ₑ) ≤
      ENNReal.ofReal |a⁻¹| * ∫⁻ x, ‖f (x+(e w:Euc n))-f x‖ₑ := by
  simp only [chartFiber,← mul_sub,enorm_mul,map_add]
  rw [Real.enorm_eq_ofReal_abs (a⁻¹)]
  have hfib := planeFiber_measurable hm v
  have hdiff : Measurable (fun y : normalPlane v ↦ ‖planeFiber v f (y+e w)-planeFiber v f y‖ₑ) :=
    ((hfib.comp (measurable_id.add measurable_const)).sub hfib).enorm
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    e.measurePreserving.lintegral_comp hdiff]
  exact mul_le_mul le_rfl (planeFiber_translation_le hm hf hv (e w)) zero_le zero_le

end RPISingularHarnack

end

end OAI
