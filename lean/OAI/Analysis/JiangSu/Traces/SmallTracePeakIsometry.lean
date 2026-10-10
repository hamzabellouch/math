import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.SmallTraceCutRanks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzPeakSupport
import OAI.Analysis.JiangSu.Comparison.ScalarStrictComparison

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_directPositiveCut_le_one {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a : A) (ha : 0≤a) (han : ‖a‖≤1)
    (α : ℝ) (hα : 0≤α) : ‖directPositiveCut α a‖≤1 := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := hA
    simp only [Subsingleton.elim (directPositiveCut α a) 0,norm_zero,zero_le_one]
  have := hA
  apply norm_cfc_le (by norm_num : (0:ℝ)≤1)
  intro t ht
  change |max (t-α) 0|≤1
  rw [abs_of_nonneg (le_max_right _ _)]
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  have ht1 : t≤1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ht0] using
      (spectrum.norm_le_norm_of_mem ht).trans han
  exact max_le (by linarith) zero_le_one

theorem small_trace_peak_isometry [Nonempty (TracialState A)]
    (hcmp : StrictComparison A) (e f : A) (he : 0≤e) (hen : ‖e‖≤1)
    (hf : 0≤f) (hfn : ‖f‖≤1) (α δ c ε : ℝ)
    (hα : 0<α) (hδ : 0<δ) (hc : 0<c) (hε : 0<ε) (hε1 : ε≤1)
    (hsmall : ∀ τ : TracialState A, (τ.functional e).re<α*c/2)
    (hlarge : ∀ τ : TracialState A, c≤(τ.functional f).re)
    (hdefect : ∀ τ : TracialState A, (τ.functional (f-f*f)).re<δ*c/2) :
    ∃ s : A, ‖s‖≤2 ∧ ‖star s*s-e‖<ε+α ∧ ‖f*s-s‖≤2*δ := by
  let a := directPositiveCut α e
  let b := directPositiveCut (1-δ) f
  have ha : 0≤a := directPositiveCut_nonneg _ _
  have hb : 0≤b := directPositiveCut_nonneg _ _
  have hgap (τ : TracialState A) : normalizedRootRank τ a<normalizedRootRank τ b := by
    apply (ENNReal.toReal_lt_toReal (directRank_ne_top τ a ha)
      (directRank_ne_top τ b hb)).mp
    have h1 := directPositiveCut_rank_le_trace_div τ e he α hα
    have h2 := peak_cut_rank_lower τ f hf hfn δ hδ
    have hs : (τ.functional e).re/α<c/2 := by
      apply (div_lt_iff₀ hα).mpr
      nlinarith [hsmall τ]
    have hd : (τ.functional (f-f*f)).re/δ<c/2 := by
      apply (div_lt_iff₀ hδ).mpr
      nlinarith [hdefect τ]
    change (normalizedRootRank τ a).toReal≤_ at h1
    change _≤(normalizedRootRank τ b).toReal at h2
    linarith [hlarge τ]
  have hb0 : b≠0 := by
    intro hz
    let τ : TracialState A := Classical.choice inferInstance
    have hlower := peak_cut_rank_lower τ f hf hfn δ hδ
    have hdefect_bound : (τ.functional (f-f*f)).re/δ<c/2 := by
      apply (div_lt_iff₀ hδ).mpr
      nlinarith [hdefect τ]
    change _≤(normalizedRootRank τ b).toReal at hlower
    rw [hz,normalizedRootRank_zero,ENNReal.toReal_zero] at hlower
    linarith [hlarge τ, hc]
  have hab := hcmp.scalar a b ha hb hb0 hgap
  obtain ⟨s,hsn,hsa,hfs⟩ := approximate_peak_isometry a f
    (norm_directPositiveCut_le_one e he hen α hα.le) hf hfn δ hδ.le hab ε hε hε1
  refine ⟨s,hsn,?_,hfs⟩
  have hec := norm_sub_directPositiveCut_le e he α hα.le
  have ht := norm_sub_le_norm_sub_add_norm_sub (star s*s) a e
  rw [norm_sub_rev e a] at hec
  linarith

end DirectComparison

end
end

end OAI
