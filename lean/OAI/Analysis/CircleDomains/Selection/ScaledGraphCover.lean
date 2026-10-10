import OAI.Analysis.CircleDomains.Selection.GraphCylinderCover
import Mathlib.Analysis.Normed.Group.Basic

namespace OAI

/-! Affine dilation of a graph cover retains its diameter and cost
factors. The metric is the sup metric on the base and the vertical axis. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def graphAffine (c : ℝ × ℝ) (t s : ℝ) (p : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ :=
  (c+s • p.1,t+s*p.2)

lemma graphAffine_lipschitz (c : ℝ × ℝ) (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    LipschitzWith ⟨s,hs⟩ (graphAffine c t s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist ((c,t)+s • x) ((c,t)+s • y) ≤ s*dist x y
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hs]

lemma scaled_graph_cover {ι : Type*} [Countable ι]
    (T : ι → Set ((ℝ × ℝ) × ℝ)) (c : ℝ × ℝ) (t : ℝ) {s D : ℝ}
    (hs : 0 < s) (hdiam : ∀ i, ediam (T i) ≤ ENNReal.ofReal D)
    {A : Set ((ℝ × ℝ) × ℝ)} (hcover : A ⊆ ⋃ i, T i) :
    graphAffine c t s '' A ⊆ ⋃ i, graphAffine c t s '' T i ∧
    (∀ i, ediam (graphAffine c t s '' T i) ≤ ENNReal.ofReal (s*D)) ∧
    (∑' i, ediam (graphAffine c t s '' T i)^2) ≤
      ENNReal.ofReal (s^2) * ∑' i, ediam (T i)^2 := by
  have hL := graphAffine_lipschitz c t hs.le
  refine ⟨?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i,mem_image_of_mem _ hi⟩
  · intro i
    calc
      _ ≤ ENNReal.ofReal s * ediam (T i) := by
        simpa only [ENNReal.ofReal_eq_coe_nnreal hs.le, NNReal.mk] using hL.ediam_image_le (T i)
      _ ≤ ENNReal.ofReal s * ENNReal.ofReal D := mul_le_mul' le_rfl (hdiam i)
      _ = _ := (ENNReal.ofReal_mul hs.le).symm
  · calc
      _ ≤ ∑' i, (ENNReal.ofReal s * ediam (T i))^2 := by
        apply ENNReal.tsum_le_tsum
        intro i
        apply pow_le_pow_left'
        simpa only [ENNReal.ofReal_eq_coe_nnreal hs.le, NNReal.mk] using hL.ediam_image_le (T i)
      _ = ENNReal.ofReal (s^2) * ∑' i, ediam (T i)^2 := by
        simp only [mul_pow, ← ENNReal.ofReal_pow hs.le]
        exact ENNReal.tsum_mul_left

end CircleDomainRigidity

end

end OAI
