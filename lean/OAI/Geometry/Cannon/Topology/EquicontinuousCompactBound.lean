import Mathlib

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

noncomputable section
open Set Metric Filter Topology

noncomputable section
open Set Filter Topology Metric

noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ENNReal

noncomputable section
open Set Metric Filter Topology

namespace CannonPlane

lemma equicontinuous_compact_bound {ι : Type*} (F : ι → ℂ → ℂ)
    (he : Equicontinuous F) (hb : ∀ z, ∃ B : ℝ, ∀ i, ‖F i z‖ ≤ B)
    {S : Set ℂ} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i z, z ∈ S → ‖F i z‖ ≤ B := by
  classical
  have hlocal (z : ℂ) : ∃ r : ℝ, 0 < r ∧ ∀ w, dist w z < r → ∀ i, dist (F i w) (F i z) < 1 := by
    obtain ⟨r,hr,h⟩ := Metric.equicontinuousAt_iff.mp (he z) 1 (by norm_num)
    exact ⟨r,hr,fun w hw i => by simpa only [dist_comm] using h w hw i⟩
  choose r hr hh using hlocal
  choose B hB using hb
  obtain ⟨t,hts,hcover⟩ := hS.elim_nhds_subcover (fun z => ball z (r z))
    (fun z _ => ball_mem_nhds z (hr z))
  refine ⟨∑ z ∈ t, (max (B z) 0+1),Finset.sum_nonneg (fun z _ => by positivity),?_⟩
  intro i w hw
  obtain ⟨z,hzt,hwz⟩ := mem_iUnion₂.mp (hcover hw)
  have hdist := hh z w hwz i
  have htri : ‖F i w‖ ≤ dist (F i w) (F i z)+‖F i z‖ := by
    simpa only [dist_zero_right] using dist_triangle (F i w) (F i z) 0
  have hle : ‖F i w‖ ≤ max (B z) 0+1 := by linarith [hB z i,le_max_left (B z) 0]
  exact hle.trans (Finset.single_le_sum (f:=fun x => max (B x) 0+1) (fun x _ => by positivity) hzt)

end CannonPlane

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
