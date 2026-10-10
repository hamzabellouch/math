import OAI.Probability.ContinuumTransition.TripleState

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

structure ConstructionCap (t M : ℝ) : Prop where
  t_large : 1 < t
  mass_pos : 0 < M
  strong : 140608*kernelHeight*M ≤ t
  gap : 1024*M < t

lemma ConstructionCap.weak {t M m : ℝ} (h : ConstructionCap t M) (hm : m ≤ M) :
    17576*kernelHeight*m ≤ t := by
  calc
    17576*kernelHeight*m ≤ 17576*kernelHeight*M := mul_le_mul_of_nonneg_left hm (by positivity [kernelHeight_pos])
    _ ≤ 140608*kernelHeight*M := by nlinarith only [mul_pos kernelHeight_pos h.mass_pos]
    _ ≤ t := h.strong

lemma ConstructionCap.small {t M m : ℝ} (h : ConstructionCap t M) (hm : m ≤ M) :
    2197*t*kernelHeight*m ≤ (t^2/8)/8 := by
  apply strong_smallness (lt_trans zero_lt_one h.t_large)
  exact (mul_le_mul_of_nonneg_left hm (by positivity [kernelHeight_pos])).trans h.strong

lemma ConstructionCap.lt_gap {t M a : ℝ} (h : ConstructionCap t M) (ha : a ≤ M) :
    1024*a < t := (mul_le_mul_of_nonneg_left ha (by norm_num)).trans_lt h.gap

lemma exists_constructionCap {M : ℝ} (hM : 0 < M) : ∃ T : ℝ, ConstructionCap T M := by
  obtain ⟨T,hT⟩ := exists_gt (max 1 (max (140608*kernelHeight*M) (1024*M)))
  refine ⟨T,?_,hM,?_,?_⟩
  · exact (le_max_left _ _).trans_lt hT
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hT.le
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hT

lemma ConstructionCap.mono_t {t T M : ℝ} (h : ConstructionCap T M) (ht : T ≤ t) :
    ConstructionCap t M := ⟨h.t_large.trans_le ht,h.mass_pos,h.strong.trans ht,h.gap.trans_le ht⟩

end ContinuumTemperature
end
end

end OAI
