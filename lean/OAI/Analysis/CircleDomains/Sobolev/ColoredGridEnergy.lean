import OAI.Analysis.CircleDomains.Transfer.GraphGridCells
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

namespace OAI

/-! The enlarged graph-grid balls have a uniform energy sum, with no
doubling hypothesis on the measure. -/
open Set Function MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma colored_grid_energy_sum (μ : Measure GraphSpace) {s : ℝ} (hs : 0 < s)
    (r : GraphGridColor) (I : Set GraphGridIndex) (c : I → GraphSpace)
    (hc : ∀ i : I, c i ∈ graphGridCell r (i : GraphGridIndex) s) {O : Set GraphSpace}
    (hO : ∀ i : I, closedBall (c i) (4*s) ⊆ O) :
    (∑' i : I, μ (closedBall (c i) (4*s))) ≤ μ O := by
  have hd : Pairwise (Disjoint on (fun i : I => closedBall (c i) (4*s))) := by
    intro i j hij
    exact graphGridCell_enlarged_disjoint hs r (Subtype.coe_ne_coe.mpr hij) (hc i) (hc j)
  rw [← measure_iUnion hd (fun _ => isClosed_closedBall.measurableSet)]
  exact measure_mono (iUnion_subset hO)

lemma all_colored_grid_energy_sum (μ : Measure GraphSpace) {s : ℝ} (hs : 0 < s)
    (I : GraphGridColor → Set GraphGridIndex) (c : (r : GraphGridColor) → I r → GraphSpace)
    (hc : ∀ (r : GraphGridColor) (i : I r), c r i ∈ graphGridCell r (i : GraphGridIndex) s) {O : Set GraphSpace}
    (hO : ∀ (r : GraphGridColor) (i : I r), closedBall (c r i) (4*s) ⊆ O) :
    (∑' r, ∑' i : I r, μ (closedBall (c r i) (4*s))) ≤ 4096 * μ O := by
  calc
    _ ≤ ∑' _r : GraphGridColor, μ O :=
      ENNReal.tsum_le_tsum (fun r => colored_grid_energy_sum μ hs r (I r) (c r) (hc r) (hO r))
    _ = _ := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      norm_num

end CircleDomainRigidity

end

end OAI
