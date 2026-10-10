import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.Ranks

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem directPositiveCut_rank_le_trace_add_defect_div
    (τ : TracialState A) (a : A) (ha : 0≤a) (han : ‖a‖≤1)
    (α : ℝ) (hα : 0<α) :
    (normalizedRootRank τ (directPositiveCut α a)).toReal ≤
      (τ.functional a).re+(τ.functional (a-a*a)).re/α := by
  have : Nontrivial A := ⟨⟨0,1,fun h => zero_ne_one (by
    simpa only [map_zero,τ.normalized] using congrArg τ.functional h)⟩⟩
  have hnon := (τ.functional.map_nonneg (positive_contraction_defect_nonneg ha han)).1
  have hr : normalizedRootRank τ (directPositiveCut α a) ≤
      ENNReal.ofReal ((τ.functional a).re+(τ.functional (a-a*a)).re/α) := by
    rw [←cutoffTraceSup_eq_rank τ _ (directPositiveCut_nonneg _ _)]
    apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    have he : spectralApproxUnit (directPositiveCut α a) n≤a+α⁻¹ • (a-a*a) := by
      have heq : a+α⁻¹ • (a-a*a)=cfc (fun t : ℝ => t+α⁻¹*(t-t*t)) a := by
        rw [cfc_add (a := a) _ _ (by fun_prop) (by fun_prop),
          cfc_const_mul _ _ a (by fun_prop),cfc_sub _ _ a (by fun_prop) (by fun_prop),
          cfc_mul _ _ a (by fun_prop) (by fun_prop),cfc_id' ℝ a ha.isSelfAdjoint]
      rw [heq]
      change cfc (fun t : ℝ => min (((n:ℝ)+1)*t) 1)
        (cfc (fun t : ℝ => max (t-α) 0) a)≤_
      rw [←cfc_comp _ _ a ha.isSelfAdjoint]
      apply cfc_mono (hf := by fun_prop) (hg := by fun_prop)
      intro t ht
      change min (((n:ℝ)+1)*max (t-α) 0) 1≤t+α⁻¹*(t-t*t)
      have ht0 := spectrum_nonneg_of_nonneg ha ht
      have ht1 : t≤1 := ((le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)).trans han
      have htt : 0≤t-t*t := by
        simpa only [mul_sub, mul_one] using mul_nonneg ht0 (sub_nonneg.mpr ht1)
      by_cases hcut : t≤α
      · rw [max_eq_right (sub_nonpos.mpr hcut),mul_zero,min_eq_left zero_le_one]
        positivity
      · apply (min_le_right _ _).trans
        have hmul : α≤α*t+(t-t*t) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (le_of_not_ge hcut))]
        have hh := (div_le_div_iff_of_pos_right hα).mpr hmul
        simpa only [add_div,mul_div_cancel_left₀ _ (ne_of_gt hα),div_self (ne_of_gt hα),
          inv_mul_eq_div] using hh
    have ht := (τ.functional.monotone he).1
    change (τ.functional (spectralApproxUnit (directPositiveCut α a) n)).re≤
      (τ.functional (a+α⁻¹ • (a-a*a))).re at ht
    simpa only [map_add,Complex.add_re,τ.functional.map_smul_of_tower,
      Complex.smul_re,smul_eq_mul,inv_mul_eq_div] using ht
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
  rwa [ENNReal.toReal_ofReal (add_nonneg (τ.functional.map_nonneg ha).1
    (div_nonneg hnon hα.le))] at hreal

end DirectComparison

end
end

end OAI
