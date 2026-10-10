import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.ProjectionDefectRankUpper
import OAI.Analysis.JiangSu.Traces.SmallTracePeakIsometry

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem projection_gap_isometry [Nonempty (TracialState A)]
    (hcmp : StrictComparison A) (e f : A) (he : 0≤e) (hen : ‖e‖≤1)
    (hf : 0≤f) (hfn : ‖f‖≤1) (α δ c ε : ℝ)
    (hα : 0<α) (hδ : 0<δ) (hc : 0<c) (hε : 0<ε) (hε1 : ε≤1)
    (hgap : ∀ τ : TracialState A, (τ.functional e).re+c≤(τ.functional f).re)
    (hede : ∀ τ : TracialState A, (τ.functional (e-e*e)).re<α*c/3)
    (hfde : ∀ τ : TracialState A, (τ.functional (f-f*f)).re<δ*c/3) :
    ∃ s : A, ‖s‖≤2 ∧ ‖star s*s-e‖<ε+α ∧ ‖f*s-s‖≤2*δ := by
  let a := directPositiveCut α e
  let b := directPositiveCut (1-δ) f
  have ha : 0≤a := directPositiveCut_nonneg _ _
  have hb : 0≤b := directPositiveCut_nonneg _ _
  have hcmpgap (τ : TracialState A) : normalizedRootRank τ a<normalizedRootRank τ b := by
    apply (ENNReal.toReal_lt_toReal (directRank_ne_top τ a ha)
      (directRank_ne_top τ b hb)).mp
    have h1 := directPositiveCut_rank_le_trace_add_defect_div τ e he hen α hα
    have h2 := peak_cut_rank_lower τ f hf hfn δ hδ
    have hs : (τ.functional (e-e*e)).re/α<c/3 := by
      apply (div_lt_iff₀ hα).mpr
      nlinarith [hede τ]
    have hd : (τ.functional (f-f*f)).re/δ<c/3 := by
      apply (div_lt_iff₀ hδ).mpr
      nlinarith [hfde τ]
    change (normalizedRootRank τ a).toReal≤_ at h1
    change _≤(normalizedRootRank τ b).toReal at h2
    linarith [hgap τ]
  have hb0 : b≠0 := by
    intro hz
    let τ : TracialState A := Classical.choice inferInstance
    have h := hcmpgap τ
    rw [hz,normalizedRootRank_zero] at h
    exact not_lt_of_ge zero_le h
  have hab := hcmp.scalar a b ha hb hb0 hcmpgap
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
