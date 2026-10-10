import OAI.Analysis.Pureness.Completion.CompletedRankComparison
import OAI.Analysis.Pureness.Operators.PositiveOrderComparison

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma CuntzSubequiv.inr {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] {a b : D} (hab : CuntzSubequiv a b) :
    CuntzSubequiv (a : Unitization ℂ D) (b : Unitization ℂ D) := by
  obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence a b).mp hab
  apply (cuntzSubequiv_iff_sequence _ _).mpr
  refine ⟨fun j => (v j : Unitization ℂ D), ?_⟩
  simpa only [Function.comp_def, Unitization.inr_mul, Unitization.inr_star] using
    (Unitization.continuous_inr (𝕜 := ℂ)).continuousAt.tendsto.comp hv

theorem CuntzSubequiv.completedRank_le {a b : CornerCompletion A}
    (hab : CuntzSubequiv a b) (ha : 0 ≤ a) (hb : 0 ≤ b) (τ : TracialState A) :
    completedRootRank τ a ≤ completedRootRank τ b :=
  completedRootRank_le_of_unitized_cuntz τ a b ha hb hab.inr

theorem completedRootRank_cut_le (τ : TracialState A) (k : ℕ)
    (a : CornerCompletion A) (ha : 0 ≤ a) :
    completedRootRank τ (completedCornerCut A k a) ≤ completedRootRank τ a :=
  (completedCornerCut_cuntz A k a).completedRank_le (completedCornerCut_nonneg A k a ha) ha τ

theorem completedRootRank_eq_iSup_cuts (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    completedRootRank τ a = ⨆ k : ℕ, completedRootRank τ (completedCornerCut A (k + 1) a) := by
  apply le_antisymm (completedRootRank_le_iSup_cuts τ a ha)
  exact iSup_le fun k => completedRootRank_cut_le τ (k + 1) a ha

theorem completedRootRank_cuts_tendsto (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Tendsto (fun k : ℕ => completedRootRank τ (completedCornerCut A (k + 1) a))
      atTop (𝓝 (completedRootRank τ a)) := by
  rw [completedRootRank_eq_iSup_cuts τ a ha]
  exact tendsto_atTop_iSup (completedRootRank_cut_monotone τ a ha)

theorem completedRootRank_mono_positive (τ : TracialState A) (a b : CornerCompletion A)
    (ha : 0 ≤ a) (hab : a ≤ b) : completedRootRank τ a ≤ completedRootRank τ b := by
  apply completedRootRank_le_of_unitized_cuntz τ a b ha (ha.trans hab)
  exact cuntzSubequiv_of_nonneg_of_le _ _ (Unitization.inr_nonneg_iff.mpr ha)
    (Unitization.inr_le_inr_iff.mpr hab)

theorem completedRootRank_polar (τ : TracialState A) (x : CornerCompletion A) :
    completedRootRank τ (star x * x) = completedRootRank τ (x * star x) := by
  have hle (x : CornerCompletion A) :
      completedRootRank τ (star x * x) ≤ completedRootRank τ (x * star x) := by
    apply completedRootRank_le_of_unitized_cuntz τ _ _ (star_mul_self_nonneg _) (mul_star_self_nonneg _)
    simpa only [Unitization.inr_mul, Unitization.inr_star] using
      star_mul_self_cuntzSubequiv (x : Unitization ℂ (CornerCompletion A))
  exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))
end CuntzPureness

end

end OAI
