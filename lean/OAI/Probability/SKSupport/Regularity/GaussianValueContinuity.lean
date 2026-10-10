import Mathlib
import OAI.Probability.SKSupport.Parabolic.VarianceTilted

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma varianceLogHeat_time_continuous {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c x : ℝ) :
    Continuous (fun t => varianceLogHeat c t f x) := by
  by_cases hc : c=0
  · subst c
    simpa only [varianceLogHeat,↓reduceIte] using
      continuous_varianceHeat hf.smooth.continuous (exponentialBound_of_lipschitz hLip) x
  · change Continuous (fun t => if c=0 then _ else _)
    simp only [hc,↓reduceIte]
    exact ((continuous_varianceHeat (Real.continuous_exp.comp (continuous_const.mul hf.smooth.continuous))
      (exponentialBound_exp hLip c) x).log
      (fun t => ne_of_gt (varianceHeat_exp_pos hLip c t x))).div_const c

lemma varianceLogHeat_joint_continuous {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ × ℝ => varianceLogHeat c p.1 f p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let F := fun q : ℝ × ℝ => varianceLogHeat c q.1 f q.2
  have hlim : Tendsto (fun q : ℝ × ℝ => (K:ℝ)*|q.2-p.2|+
      |varianceLogHeat c q.1 f p.2-varianceLogHeat c p.1 f p.2|) (𝓝 p) (𝓝 0) := by
    have hh : Continuous (fun q : ℝ × ℝ => (K:ℝ)*|q.2-p.2|+
        |varianceLogHeat c q.1 f p.2-varianceLogHeat c p.1 f p.2|) := by
      exact (continuous_const.mul (continuous_snd.sub continuous_const).abs).add
        (((varianceLogHeat_time_continuous hf hLip c p.2).comp continuous_fst).sub continuous_const).abs
    simpa only [sub_self,abs_zero,mul_zero,add_zero] using hh.continuousAt.tendsto (x := p)
  change Tendsto (fun q : ℝ × ℝ => varianceLogHeat c q.1 f q.2) (𝓝 p) (𝓝 (varianceLogHeat c p.1 f p.2))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with q hq
  have hb := (varianceLogHeat_lipschitz hLip hc q.1).dist_le_mul q.2 p.2
  have htri := dist_triangle (F q) (varianceLogHeat c q.1 f p.2) (F p)
  simp only [Real.dist_eq] at hb htri ⊢
  exact (htri.trans (add_le_add hb le_rfl)).trans_lt hq

end ZeroTemperatureSK.Heat

end
end

end OAI
