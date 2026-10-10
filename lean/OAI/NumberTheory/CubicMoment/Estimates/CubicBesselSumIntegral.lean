import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselIntegral
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! The positive-quadrant Gamma integral needed for the square of the
fixed order-one-third Schlaefli kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicBesselSumWeight (s : ℝ) : ℝ := s^(-4/3:ℝ)*Real.exp (-s)

def cubicBesselTriangle (p : ℝ × ℝ) : ℝ :=
  if p.2 ∈ Ioo 0 p.1 then cubicBesselSumWeight p.1 else 0

lemma cubicBesselTriangle_nonneg (p : ℝ × ℝ) : 0 ≤ cubicBesselTriangle p := by
  unfold cubicBesselTriangle cubicBesselSumWeight
  split_ifs with hp
  · exact mul_nonneg (Real.rpow_nonneg (by linarith [hp.1,hp.2]) _) (Real.exp_pos _).le
  · rfl

lemma cubicBesselTriangle_inner_integrable (s : ℝ) :
    Integrable (fun t : ℝ => cubicBesselTriangle (s,t)) := by
  have hi : IntegrableOn (fun _ : ℝ => cubicBesselSumWeight s) (Ioo 0 s) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  convert hi.integrable_indicator measurableSet_Ioo using 1
  ext t
  simp only [cubicBesselTriangle,Set.indicator]

lemma cubicBesselTriangle_inner (s : ℝ) :
    (∫ t : ℝ, cubicBesselTriangle (s,t)) =
      if 0 < s then s^(-1/3:ℝ)*Real.exp (-s) else 0 := by
  have he : (fun t : ℝ => cubicBesselTriangle (s,t))=
      (Ioo 0 s).indicator (fun _ => cubicBesselSumWeight s) := by
    ext t
    simp only [cubicBesselTriangle,Set.indicator]
  rw [he]
  rw [integral_indicator measurableSet_Ioo,setIntegral_const,smul_eq_mul,Real.volume_real_Ioo]
  by_cases hs : 0 < s
  · rw [ite_eq_left hs,sub_zero,max_eq_left hs.le,cubicBesselSumWeight]
    have hp : s*s^(-4/3:ℝ)=s^(-1/3:ℝ) := by
      calc
        _ = s^(1:ℝ)*s^(-4/3:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hs]; norm_num
    rw [←mul_assoc,hp]
  · rw [ite_eq_right hs,sub_zero,max_eq_right (le_of_not_gt hs),zero_mul]

lemma cubicBesselTriangle_integrable :
    Integrable cubicBesselTriangle ((volume : Measure ℝ).prod volume) := by
  have hm : Measurable cubicBesselTriangle := by
    unfold cubicBesselTriangle cubicBesselSumWeight
    apply Measurable.ite ?_ (by fun_prop) measurable_const
    exact (isOpen_lt continuous_const continuous_snd).measurableSet.inter
      (isOpen_lt continuous_snd continuous_fst).measurableSet
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall cubicBesselTriangle_inner_integrable
  · have hi := integrable_laplace_rpow (by norm_num : (0:ℝ) < 2/3) (by norm_num : (0:ℝ) < 1)
    rw [←integrable_indicator_iff measurableSet_Ioi] at hi
    apply hi.congr
    filter_upwards with s
    rw [show (∫ t : ℝ, ‖cubicBesselTriangle (s,t)‖)=
        ∫ t : ℝ, cubicBesselTriangle (s,t) from integral_congr_ae
          (Filter.Eventually.of_forall (fun t => Real.norm_of_nonneg (cubicBesselTriangle_nonneg (s,t)))),
      cubicBesselTriangle_inner]
    by_cases hs : 0 < s <;> simp [Set.indicator,hs]
    congr 2
    norm_num

lemma cubicBesselTriangle_integral :
    (∫ p : ℝ × ℝ, cubicBesselTriangle p ∂((volume : Measure ℝ).prod volume))=Real.Gamma (2/3) := by
  rw [integral_prod _ cubicBesselTriangle_integrable]
  simp_rw [cubicBesselTriangle_inner]
  change (∫ s : ℝ, (Ioi 0).indicator (fun s => s^(-1/3:ℝ)*Real.exp (-s)) s)=_
  rw [integral_indicator measurableSet_Ioi]
  convert laplace_rpow (by norm_num : (0:ℝ) < 2/3) (by norm_num : (0:ℝ) < 1) using 1 <;> norm_num

def cubicBesselSumShear : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.1+p.2,p.2)
  invFun p := (p.1-p.2,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1+p.2,p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1-p.2,p.2))
    fun_prop

lemma cubicBesselSumShear_preserving :
    MeasurePreserving cubicBesselSumShear ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := measurePreserving_add_prod volume volume

lemma cubicBesselSumShear_weight (p : ℝ × ℝ) :
    cubicBesselTriangle (cubicBesselSumShear p)=
      (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)).indicator
        (fun p : ℝ × ℝ => cubicBesselSumWeight (p.1+p.2)) p := by
  have he : p.2 ∈ Ioo 0 (p.1+p.2) ↔ p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
    simp only [mem_Ioo,mem_prod,mem_Ioi]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  simp only [cubicBesselTriangle,cubicBesselSumShear,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk,he,
    Set.indicator]

lemma cubicBesselSumWeight_integrable :
    Integrable (fun p : ℝ × ℝ => cubicBesselSumWeight (p.1+p.2))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hi := cubicBesselSumShear_preserving.integrable_comp_of_integrable cubicBesselTriangle_integrable
  simp only [Function.comp_def,cubicBesselSumShear_weight] at hi
  rw [integrable_indicator_iff (measurableSet_Ioi.prod measurableSet_Ioi)] at hi
  change Integrable _ ((volume.prod volume).restrict (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))) at hi
  simpa only [Measure.prod_restrict] using hi

theorem cubicBesselSumWeight_integral :
    (∫ p : ℝ × ℝ, cubicBesselSumWeight (p.1+p.2)
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))=Real.Gamma (2/3) := by
  have he := cubicBesselSumShear_preserving.integral_comp' cubicBesselTriangle
  simp only [cubicBesselSumShear_weight] at he
  rw [integral_indicator (measurableSet_Ioi.prod measurableSet_Ioi),cubicBesselTriangle_integral] at he
  simpa only [Measure.prod_restrict] using he

end CubicFirstMoment

end

end OAI
