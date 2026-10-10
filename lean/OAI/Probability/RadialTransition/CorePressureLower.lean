import OAI.Probability.RadialTransition.CorePressureUpper

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma packing_dilated_limit {ν b : ℝ} (hν : 0 ≤ ν) :
    Tendsto (fun L : ℝ => (packingNumber L:ℝ)/((1+ν)*L+b)^3) atTop
      (nhds (packingDensity/(1+ν)^3)) := by
  have hn : (1+ν)^3 ≠ 0 := by positivity
  have hh : Tendsto (fun L : ℝ => (1+ν+b*L⁻¹)^3) atTop (nhds ((1+ν)^3)) := by
    simpa using ((tendsto_const_nhds (x := 1+ν)).add (tendsto_inv_atTop_zero.const_mul b)).pow 3
  apply (packingDensity_limit.div hh hn).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have he : 1+ν+b*L⁻¹ = ((1+ν)*L+b)/L := by field_simp
  dsimp only [Pi.div_apply]
  rw [he, div_pow]
  field_simp

lemma corePressure_packing_lower {ν b t β h : ℝ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hν : 0 ≤ ν) (hsep : 1/t+4*b ≤ ν) (hβ : 0 ≤ β) :
    packingDensity/(1+ν)^3 * (Real.log (grandOn (corePotential t) (cube b) β (t*h))/t) ≤
      grandPressure (corePotential t) t β h := by
  have ht0 : 0 < t := by linarith
  have hc := continuous_corePotential t
  have hbound := bounded_corePotential t
  have hstable := stable_corePotential t
  have hlocal := (grandOn_bounds hc hbound hstable hβ (by rw [volume_cube]; finiteness : volume (cube b) ≠ ⊤) (t*h)).1
  have hlimL : Tendsto (fun L : ℝ => (1+ν)*L+b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop (by linarith : 0 < 1+ν) tendsto_id)
  have hright := ((grandPressure_spec hc hbound hstable ht0 hβ (core_nonpos_outer ht) h).1).comp hlimL
  have hleft := (packing_dilated_limit (b := b) hν).mul_const
    (Real.log (grandOn (corePotential t) (cube b) β (t*h))/t)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have hS : 0 < (1+ν)*L+b := by positivity
  have hprod := core_grand_packing_lower (L := L) ht0 hb hν hsep hβ (h := h)
  have hlog := Real.log_le_log (pow_pos (show 0 < grandOn (corePotential t) (cube b) β (t*h) by linarith) _) hprod
  rw [Real.log_pow] at hlog
  rw [grandOn_cube] at hlog
  rw [grandOn_cube] at hlog
  have hden : 0 < t*((1+ν)*L+b)^3 := by positivity
  dsimp only [finiteGrandPressure, Function.comp_def]
  apply (le_div_iff₀ hden).mpr
  rw [grandOn_cube]
  calc
    _ = (packingNumber L:ℝ)*Real.log (grandPartition (corePotential t) t b β h) := by
      field_simp
    _ ≤ _ := hlog

end RadialTransition
end

end OAI
