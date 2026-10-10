import OAI.Geometry.RCD.Heat.CompactHeatMeasure

namespace OAI

/-! # Finite mass of the constructed heat measure -/

open Set MeasureTheory Metric TopologicalSpace
open scoped NNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [(hausdorff n X).Regular]

/-- The Markov bound gives mass at most one on every compact set. -/
theorem heatRadonMeasure_compact_le_one (t : ℝ) (ht : 0 < t) (x : X)
    {S : Set X} (hS : IsCompact S) : hX.heatRadonMeasure hn p t ht x S ≤ 1 := by
  obtain ⟨f, hf, hfc, _, hfrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hS isOpen_univ (subset_univ S)
  let F : C_c(X, ℝ) := ⟨f, hfc⟩
  have hm := RealRMK.rieszMeasure_le_of_eq_one (hX.compactHeatEval hn p t ht x)
    (f := F) (fun y => (hfrange y).1) hS hf
  have hF : |hX.compactHeatEval hn p t ht x F| ≤ 1 :=
    hX.compactHeatEval_abs_le hn p t ht x F 1 (fun y => by
      change |f y| ≤ 1
      rw [abs_of_nonneg (hfrange y).1]; exact (hfrange y).2)
  exact hm.trans (by simpa only [ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hF))

/-- The constructed Radon measure is a subprobability measure. -/
theorem heatRadonMeasure_mass_le_one (t : ℝ) (ht : 0 < t) (x : X) :
    hX.heatRadonMeasure hn p t ht x univ ≤ 1 := by
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  exact iSup_le fun S => iSup_le fun _ => iSup_le fun hS =>
    hX.heatRadonMeasure_compact_le_one hn p t ht x hS

instance heatRadonMeasure_finite (t : ℝ) (ht : 0 < t) (x : X) :
    IsFiniteMeasure (hX.heatRadonMeasure hn p t ht x) :=
  ⟨(hX.heatRadonMeasure_mass_le_one hn p t ht x).trans_lt (by norm_num)⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
