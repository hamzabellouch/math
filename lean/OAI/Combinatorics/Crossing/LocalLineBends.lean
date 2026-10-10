import OAI.Combinatorics.Crossing.ParallelDirection
import OAI.Combinatorics.Crossing.FiniteEventualRadius
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem segment_direction_of_local_line (a b d : Plane) (U : Set Plane)
    (hU : IsOpen U) (hb : b ∈ U)
    (hline : ∀ z ∈ U, z ∈ segment ℝ b a → det2 d (z-b)=0) :
    det2 d (a-b)=0 := by
  have hc : Continuous (fun t : ℝ => segmentPoint b a t) := by dsimp [segmentPoint]; fun_prop
  have hh : ∀ᶠ t : ℝ in 𝓝 0, segmentPoint b a t ∈ U := by
    exact hc.continuousAt.eventually (by simpa using hU.mem_nhds hb)
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff.mp hh
  let t : ℝ := min (r/2) (1/2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htr : t < r := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hm : segmentPoint b a t ∈ U := hs (by simpa [Real.dist_eq,abs_of_pos ht] using htr)
  have hseg : segmentPoint b a t ∈ segment ℝ b a := by
    rw [← Path.range_segment]
    exact ⟨⟨t,⟨ht.le,ht1⟩⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]⟩
  have he := hline _ hm hseg
  have heq : segmentPoint b a t-b=t • (a-b) := by
    apply Prod.ext <;> dsimp [segmentPoint] <;> ring
  rw [heq,det2_smul_right] at he
  exact (mul_eq_zero.mp he).resolve_left (ne_of_gt ht)

theorem bend_det_zero_of_local_line (a b c d : Plane) (hd : d ≠ 0)
    (U : Set Plane) (hU : IsOpen U) (hb : b ∈ U)
    (hline : ∀ z ∈ U, z ∈ segment ℝ a b ∪ segment ℝ b c → det2 d (z-b)=0) :
    det2 (b-a) (c-b)=0 := by
  have ha := segment_direction_of_local_line a b d U hU hb (by
    intro z hz hs
    exact hline z hz (Or.inl (by simpa only [segment_symm ℝ b a] using hs)))
  have hc := segment_direction_of_local_line c b d U hU hb (fun z hz hs => hline z hz (Or.inr hs))
  have hba : b-a=-(a-b) := by abel
  rw [hba,vector_parallel_of_det_zero d (a-b) hd ha,
    vector_parallel_of_det_zero d (c-b) hd hc,det2_neg_left,
    det2_smul_left,det2_smul_right,det2_self]
  ring

end Zarankiewicz

end

end OAI
