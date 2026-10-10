import OAI.Analysis.CircleDomains.Selection.ContinuousRunningMaximum
import OAI.Analysis.CircleDomains.Topology.LooplessPath
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! Continuous monotone coordinates on a loopless path. Prefix distances
separate distinct fibers; running maxima are constant on every pause. -/
open Set Function Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def prefixDistance (g : C(unitInterval, X)) (a : unitInterval) : C(unitInterval, ℝ) :=
  ⟨fun t => min 1 (infDist (g t) (g '' Iic a)),
    continuous_const.min ((continuous_infDist_pt (g '' Iic a)).comp g.continuous)⟩

lemma prefixDistance_nonneg (g : C(unitInterval, X)) (a t : unitInterval) :
    0 ≤ prefixDistance g a t := le_min zero_le_one infDist_nonneg

lemma prefixDistance_le_one (g : C(unitInterval, X)) (a t : unitInterval) :
    prefixDistance g a t ≤ 1 := min_le_left _ _

lemma prefixDistance_eq_zero (g : C(unitInterval, X)) {a t : unitInterval} (ht : t ≤ a) :
    prefixDistance g a t = 0 := by
  change min 1 (infDist (g t) (g '' Iic a)) = 0
  rw [infDist_zero_of_mem (mem_image_of_mem g ht), min_eq_right zero_le_one]

lemma prefixDistance_pos (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    {a t : unitInterval} (hat : a ≤ t) (hne : g a ≠ g t) :
    0 < prefixDistance g a t := by
  apply lt_min zero_lt_one
  have hc : IsClosed (g '' Iic a) := (isClosed_Iic.isCompact.image g.continuous).isClosed
  rw [← infDist_pos_iff_notMem_closure (s := g '' Iic a) ⟨g 0, mem_image_of_mem g (show (0 : unitInterval) ≤ a from bot_le)⟩, hc.closure_eq]
  rintro ⟨u, hu, heq⟩
  exact hne ((hloop u t (hu.trans hat) heq a ⟨hu, hat⟩).trans heq)

lemma prefixRunning_eq_zero (g : C(unitInterval, X)) {a t : unitInterval} (ht : t ≤ a) :
    runningMaximum (prefixDistance g a) t = 0 := by
  apply le_antisymm _ (runningMaximum_nonneg _ _)
  exact runningMaximum_le _ (prefixDistance_nonneg g a) le_rfl
    (fun u hu => (prefixDistance_eq_zero g (hu.trans ht)).le)

lemma prefixRunning_eq_of_loop (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    (a : unitInterval) {s t : unitInterval} (hst : s ≤ t) (heq : g s = g t) :
    runningMaximum (prefixDistance g a) s = runningMaximum (prefixDistance g a) t := by
  apply runningMaximum_eq_of_constant _ (prefixDistance_nonneg g a) hst
  intro u hu
  change min 1 (infDist (g u) _) = min 1 (infDist (g s) _)
  rw [hloop s t hst heq u hu]

lemma dense_prefix_separates (g : C(unitInterval, X)) {s t : unitInterval}
    (hst : s < t) (hne : g s ≠ g t) :
    ∃ n, s < denseSeq unitInterval n ∧ denseSeq unitInterval n < t ∧
      g (denseSeq unitInterval n) ≠ g t := by
  by_contra! hall
  have hd : Ioo s t ∩ range (denseSeq unitInterval) ⊆ {u | g u = g t} := by
    rintro u ⟨hu, n, rfl⟩
    exact hall n hu.1 hu.2
  have hclosed : IsClosed {u | g u = g t} := isClosed_eq g.continuous continuous_const
  exact hne (closure_minimal hd hclosed (dense_interval_closure hst ⟨le_rfl, hst.le⟩))

end CircleDomainRigidity

end

end OAI
