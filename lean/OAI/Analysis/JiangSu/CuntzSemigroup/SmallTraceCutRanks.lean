import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.Ranks
import OAI.Analysis.JiangSu.Nonunital.Hereditary

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem directPositiveCut_rank_le_trace_div (τ : TracialState A) (a : A) (ha : 0≤a)
    (δ : ℝ) (hδ : 0<δ) :
    (normalizedRootRank τ (directPositiveCut δ a)).toReal≤(τ.functional a).re/δ := by
  have hr : normalizedRootRank τ (directPositiveCut δ a)≤
      ENNReal.ofReal ((τ.functional a).re/δ) := by
    rw [←cutoffTraceSup_eq_rank τ _ (directPositiveCut_nonneg _ _)]
    apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    have he : spectralApproxUnit (directPositiveCut δ a) n≤δ⁻¹ • a := by
      change cfc (fun t : ℝ => min (((n:ℝ)+1)*t) 1)
        (cfc (fun t : ℝ => max (t-δ) 0) a) ≤ _
      rw [←cfc_comp _ _ a ha.isSelfAdjoint,←cfc_const_mul_id δ⁻¹ a]
      apply cfc_mono (hf := by fun_prop) (hg := by fun_prop)
      intro t ht
      have ht0 := spectrum_nonneg_of_nonneg ha ht
      change min (((n:ℝ)+1)*max (t-δ) 0) 1≤δ⁻¹*t
      by_cases htδ : t≤δ
      · rw [max_eq_right (sub_nonpos.mpr htδ),mul_zero,min_eq_left zero_le_one]
        positivity
      · apply (min_le_right _ _).trans
        rw [inv_mul_eq_div]
        exact (le_div_iff₀ hδ).mpr (by linarith)
    have ht := (τ.functional.monotone he).1
    change (τ.functional (spectralApproxUnit (directPositiveCut δ a) n)).re ≤
      (τ.functional (δ⁻¹ • a)).re at ht
    simpa only [τ.functional.map_smul_of_tower,Complex.smul_re,smul_eq_mul,div_eq_mul_inv,
      mul_comm] using ht
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
  rwa [ENNReal.toReal_ofReal (div_nonneg (τ.functional.map_nonneg ha).1 hδ.le)] at ht

theorem peak_cut_rank_lower (τ : TracialState A) (f : A) (hf : 0≤f) (hfn : ‖f‖≤1)
    (δ : ℝ) (hδ : 0<δ) :
    (τ.functional f).re-(τ.functional (f-f*f)).re/δ≤
      (normalizedRootRank τ (directPositiveCut (1-δ) f)).toReal := by
  have : Nontrivial A := ⟨⟨0,1,fun h => zero_ne_one (by
    simpa only [map_zero,τ.normalized] using congrArg τ.functional h)⟩⟩
  let b := directPositiveCut (1-δ) f
  have hb : 0≤b := directPositiveCut_nonneg _ _
  have hc : δ⁻¹ • b≤(1:A) := by
    change δ⁻¹ • cfc (fun t : ℝ => max (t-(1-δ)) 0) f≤1
    rw [←cfc_smul δ⁻¹ _ f (by fun_prop)]
    apply (cfc_le_one_iff _ f (by fun_prop) hf.isSelfAdjoint).mpr
    intro t ht
    have ht1 : t≤1 := ((le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)).trans hfn
    change δ⁻¹*max (t-(1-δ)) 0≤1
    apply (inv_mul_le_iff₀ hδ).mpr
    exact max_le (by linarith) (by positivity)
  have hmem : δ⁻¹ • b∈hereditaryCarrier b :=
    (hereditarySubalgebra b hb).smul_mem _ (self_mem_hereditary b hb)
  have hr := trace_le_rank_of_mem_hereditary τ b (δ⁻¹ • b) hb hmem hc
  have htt := ENNReal.toReal_mono (directRank_ne_top τ b hb) hr
  rw [ENNReal.toReal_ofReal (τ.functional.map_nonneg (smul_nonneg (inv_nonneg.mpr hδ.le) hb)).1] at htt
  have he : δ • f-(f-f*f)≤b := by
    have heq : δ • f-(f-f*f)=cfc (fun t : ℝ => δ*t-(t-t*t)) f := by
      rw [cfc_sub _ _ f (by fun_prop) (by fun_prop),
        cfc_const_mul_id δ f hf.isSelfAdjoint,cfc_sub _ _ f (by fun_prop) (by fun_prop),
        cfc_mul _ _ f (by fun_prop) (by fun_prop),cfc_id' ℝ f hf.isSelfAdjoint]
    rw [heq]
    change cfc _ f≤cfc _ f
    apply cfc_mono (hf := by fun_prop) (hg := by fun_prop)
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg hf ht
    have ht1 : t≤1 := ((le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)).trans hfn
    change δ*t-(t-t*t)≤ max (t-(1-δ)) 0
    by_cases hcut : t≤1-δ
    · exact (show δ*t-(t-t*t)≤0 by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hcut)]).trans (le_max_right _ _)
    · apply (le_max_left _ _).trans'
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (le_of_not_ge hcut))]
  have ht := (τ.functional.monotone he).1
  change (τ.functional (δ • f-(f-f*f))).re≤(τ.functional b).re at ht
  simp only [map_sub,τ.functional.map_smul_of_tower,Complex.sub_re,Complex.smul_re,smul_eq_mul] at ht
  simp only [τ.functional.map_smul_of_tower,Complex.smul_re,smul_eq_mul] at htt
  have hdiv : (τ.functional f).re-(τ.functional (f-f*f)).re/δ≤δ⁻¹*(τ.functional b).re := by
    rw [inv_mul_eq_div]
    have hh : (τ.functional f).re-(τ.functional (f-f*f)).re/δ =
        (δ*(τ.functional f).re-(τ.functional (f-f*f)).re)/δ := by field_simp
    rw [hh,div_le_div_iff_of_pos_right hδ]
    simpa only [map_sub,Complex.sub_re] using ht
  exact hdiv.trans htt

end DirectComparison

end
end

end OAI
