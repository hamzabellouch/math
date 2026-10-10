import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitiveHeatDecay
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRegularHeatPole

namespace OAI

/-! Integrable small- and large-time majorants for the primitive heat kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance : Countable CubicThetaPrimitiveRow := by
  exact (show Function.Injective (fun r : CubicThetaPrimitiveRow => (r.c,r.d)) from
    fun r q h => CubicThetaPrimitiveRow.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2).countable

lemma cubicThetaPrimitiveHeat_measurable (p : ℂ × ℝ) :
    Measurable (cubicThetaPrimitiveHeat p) := by
  apply Measurable.tsum
  intro r
  unfold cubicThetaPrimitiveHeatTerm
  split_ifs <;> fun_prop

lemma cubicThetaPrimitiveMellin_measurable (p : ℂ × ℝ) (s : ℝ) :
    Measurable (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) := by
  have hm := cubicThetaPrimitiveHeat_measurable p
  fun_prop

lemma cubicThetaPrimitiveMellin_low_bound {p : ℂ × ℝ} {s C t : ℝ}
    (hC : 0≤C) (ht : t∈Ioc (0:ℝ) 1)
    (hheat : cubicThetaPrimitiveHeat p t≤C*(1+t⁻¹^2)) :
    ‖t^(s-1)*cubicThetaPrimitiveHeat p t‖≤2*C*t^(s-3) := by
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _)
    (cubicThetaPrimitiveHeat_nonneg p t))]
  have hinv : 1≤t⁻¹ := (one_le_inv₀ ht.1).mpr ht.2
  have htwo : 1+t⁻¹^2≤2*t⁻¹^2 := by nlinarith
  have hb := hheat.trans (mul_le_mul_of_nonneg_left htwo hC)
  have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.1.le (s-1))
  apply hm.trans_eq
  have he : t^(s-1)*t⁻¹^2=t^(s-3) := by
    rw [inv_pow,←Real.rpow_two,←Real.rpow_neg ht.1.le,←Real.rpow_add ht.1]
    congr 1
    ring
  calc
    t^(s-1)*(C*(2*t⁻¹^2))=2*C*(t^(s-1)*t⁻¹^2) := by ring
    _ = _ := by rw [he]

lemma cubicThetaPrimitiveMellin_high_bound {p : ℂ × ℝ} {s C t : ℝ}
    (hC : 0≤C) (hs : s≤3) (ht : 1<t)
    (hheat : cubicThetaPrimitiveHeat p t≤5*C*Real.exp (-t/2)) :
    ‖t^(s-1)*cubicThetaPrimitiveHeat p t‖≤5*C*(t^2*Real.exp (-t/2)) := by
  have ht0 : 0<t := lt_trans zero_lt_one ht
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _)
    (cubicThetaPrimitiveHeat_nonneg p t))]
  have hpow : t^(s-1)≤t^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hheat (Real.rpow_nonneg ht0.le (s-1))
  have hfac : 0≤5*C*Real.exp (-t/2) := by positivity
  have h2 := mul_le_mul_of_nonneg_right hpow hfac
  exact h1.trans (by nlinarith [h2])

lemma cubicThetaPrimitiveMellin_tail_integrable :
    IntegrableOn (fun t : ℝ => t^2*Real.exp (-t/2)) (Ioi 0) := by
  convert integrable_laplace_rpow (by norm_num : (0:ℝ)<3)
    (by norm_num : (0:ℝ)<1/2) using 1
  funext t
  rw [show (3:ℝ)-1=2 by norm_num,Real.rpow_two]
  congr 2
  ring

def cubicThetaPrimitiveMellinTailMass : ℝ :=
  ∫ t in Ioi (1:ℝ),t^2*Real.exp (-t/2)

lemma cubicThetaPrimitiveMellinTailMass_nonneg : 0≤cubicThetaPrimitiveMellinTailMass := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (sq_nonneg t) (Real.exp_pos _).le

lemma cubicThetaPrimitiveMellin_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) (hs3 : s≤3) :
    IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) (Ioi 0) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaPrimitiveHeat_small_large
  have hlow : IntegrableOn (fun t : ℝ => 2*C*t^(s-3)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<s-3))).const_mul _
  have hhigh : IntegrableOn (fun t : ℝ => 5*C*(t^2*Real.exp (-t/2))) (Ioi 1) :=
    (cubicThetaPrimitiveMellin_tail_integrable.mono_set
      (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))).const_mul _
  have hl : IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) (Ioc 0 1) := by
    apply hlow.mono' (cubicThetaPrimitiveMellin_measurable p s).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact cubicThetaPrimitiveMellin_low_bound hC ht ((hbound p hp).1 t ht.1)
  have hh : IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) (Ioi 1) := by
    apply hhigh.mono' (cubicThetaPrimitiveMellin_measurable p s).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicThetaPrimitiveMellin_high_bound hC hs3 ht ((hbound p hp).2 t ht.le)
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1)] using hl.union hh

end CubicFirstMoment

end

end OAI
