import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Local slope bounds from a neighborhood increment estimate -/

open Set Filter Metric
open scoped Topology ENNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem localSlope_le_of_eventually_increment {f : X → ℝ} {x : X} {c : ℝ}
    (h : ∀ᶠ y in 𝓝 x, |f x-f y| ≤ c*dist x y) :
    localSlope f x ≤ ENNReal.ofReal c := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp h
  unfold localSlope
  refine iInf_le_of_le r (iInf_le_of_le hr ?_)
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply iSup_le
  intro hne
  have hd : 0 < dist x y := dist_pos.mpr (Ne.symm hne)
  have hh := hball (show y ∈ ball x r by simpa only [mem_ball,dist_comm] using hy)
  change |f x-f y| ≤ c*dist x y at hh
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hd).mpr
  simpa only [abs_sub_comm] using hh

end RegularPointCoordinates

end OAI
