import OAI.Probability.FreeIsing.Trees.BranchingExtinction
import OAI.Probability.FreeIsing.Trees.ConeSurvival
import OAI.Probability.FreeIsing.Trees.PercolationFiniteness

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem367.SubcriticalClusters

theorem cone_survival_tendsto_zero {b : ℕ} (hb : 2 ≤ b) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hcritical : (b : ℝ) * p ≤ 1)
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    Tendsto (fun n => labelMeasure (b + 1) (survivalEvent id p r n))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure (labelMeasure (b + 1)) := by
    unfold labelMeasure
    infer_instance
  have h := (ENNReal.continuous_ofReal.tendsto 0).comp
    (BranchingSurvival.probability_tendsto_zero hb ⟨hp0, hp1⟩ hcritical)
  have heq : (fun n => labelMeasure (b + 1) (survivalEvent id p r n)) =
      fun n => ENNReal.ofReal (BranchingSurvival.probability b p n) := by
    funext n
    rw [← TreeConeCoding.survival_probability_real p r hr n]
    change labelMeasure (b + 1) (survivalEvent id p r n) =
      ENNReal.ofReal (labelMeasure (b + 1) (survivalEvent id p r n)).toReal
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [heq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using h

theorem ae_all_finite_openClusters_critical {d : ℕ} (hd : 3 ≤ d) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hcritical : ((d - 1 : ℕ) : ℝ) * p ≤ 1) :
    ∀ᵐ U ∂labelMeasure d, ∀ o : TreeVertex d, (openCluster p U o).Finite := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hb : 2 ≤ b := by omega
  have hcritical' : (b : ℝ) * p ≤ 1 := by simpa using hcritical
  apply ae_all_finite_openClusters_of_nonroot_survival_bound
    (labelMeasure (b + 1)) id p
    (fun r n => labelMeasure (b + 1) (survivalEvent id p r n))
  · intro r hr n
    exact le_rfl
  · intro r hr
    exact cone_survival_tendsto_zero hb hp0 hp1 hcritical' r hr

end Problem367.SubcriticalClusters

end

end OAI
