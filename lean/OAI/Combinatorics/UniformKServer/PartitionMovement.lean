import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionGeometry
import OAI.Combinatorics.UniformKServer.PrefixCounts
import OAI.Combinatorics.UniformKServer.TreeAllocationMovement

namespace OAI

                                        
section

/-! Movement of the actual allocation on the actual common tree, reduced to
literal coordinate-key edits. All addends are uniform in hidden law/horizon. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def weight (A : ActualPartitions.Config X) (v : Vertex (size A k J)) : ℝ :=
  radius A (depth (shape A k J) v)

omit [Fintype X] [MetricSpace X] in
theorem radius_step (A : ActualPartitions.Config X) (d : ℕ) :
    22*radius A (d+1)≤radius A d := by
  have hq : 22*A.q≤1 := by linarith [A.shiftH,A.P.gammaH_small]
  have h := mul_le_mul_of_nonneg_left hq (radius_nonneg A d)
  dsimp only [radius] at h ⊢
  rw [pow_succ]
  nlinarith only [h]

omit [MetricSpace X] in
theorem weight_separated (A : ActualPartitions.Config X) (v : Vertex (size A k J)) (hv : v≠0) :
    22*weight A v≤weight A ((shape A k J).parent v) := by
  unfold weight
  rw [depth_child v hv]
  exact radius_step A _

def coordinateCost (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a : Fin k,∑ i : Fin J,radius A i.val*PrefixMovement.diff
    (word A D hk z (t+1) ω (D.position (t+1) ω a) i)
    (word A D hk z t ω (D.position t ω a) i)

theorem pointwise_hidden (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ v : Vertex (size A k J), if v=0 then 0 else weight A ((shape A k J).parent v)*
      |((TreeCountData.data D (map A D hk z)).count (t+1) ω v:ℝ)-
       (TreeCountData.data D (map A D hk z)).count t ω v|)≤
    4*coordinateCost A D hk z t ω := by
  have h := PrefixMovement.count_variation
    (fun a => word A D hk z (t+1) ω (D.position (t+1) ω a))
    (fun a => word A D hk z t ω (D.position t ω a))
    (radius A) (radius_nonneg A) (fun d => by
      have := radius_step A d
      have := radius_nonneg A (d+1)
      linarith)
  change (∑ v : Vertex (size A k J),PrefixMovement.edgeWeight (radius A) (depth (shape A k J) v)*
    |((TreeCountData.data D (map A D hk z)).count (t+1) ω v:ℝ)-
       (TreeCountData.data D (map A D hk z)).count t ω v|)≤_ at h
  refine Eq.trans_le ?_ h
  apply sum_congr rfl
  intro v _
  by_cases hv : v=0
  · subst v
    rw [depth_root]
    simp [PrefixMovement.edgeWeight]
  · rw [ite_eq_right hv,PrefixMovement.edgeWeight,ite_eq_right (Nat.ne_of_gt (depth_positive A v hv))]
    simp only [weight,depth_child v hv,Nat.add_sub_cancel]

theorem hidden_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (H : ℕ) :
    hiddenCost (TreeCountData.data D (map A D hk z)) H (weight A)≤
    4*integral (TreeCountData.data D (map A D hk z)) H (coordinateCost A D hk z) := by
  let d := TreeCountData.data D (map A D hk z)
  have h := sum_le_sum (s:=range H) (fun t _ => PilotEdits.average_mono D.weight _ _
    (fun ω => (D.positive ω).le) (pointwise_hidden A D hk z t))
  change (∑ t∈range H,∑ ω,D.weight ω*(∑ v : Vertex (size A k J),if v=0 then 0 else
    weight A ((shape A k J).parent v)*|(d.count (t+1) ω v:ℝ)-d.count t ω v|))≤_ at h
  have he : hiddenCost d H (weight A)=
    ∑ t∈range H,∑ ω,D.weight ω*(∑ v : Vertex (size A k J),if v=0 then 0 else
      weight A ((shape A k J).parent v)*|(d.count (t+1) ω v:ℝ)-d.count t ω v|) := by
    have hv (v : Vertex (size A k J)) :
        (if v=0 then 0 else weight A ((shape A k J).parent v)*hiddenMove d H v)=
        ∑ t∈range H,∑ ω,D.weight ω*(if v=0 then 0 else
          weight A ((shape A k J).parent v)*|(d.count (t+1) ω v:ℝ)-d.count t ω v|) := by
      by_cases hz : v=0
      · simp only [hz,ite_true,mul_zero,sum_const_zero]
      · simp only [hz,ite_false,hiddenMove,integral,RankTracking.average,mul_sum]
        apply sum_congr rfl
        intro t _
        apply sum_congr rfl
        intro ω _
        change _*(D.weight ω*_)=D.weight ω*(_*_)
        ring
    simp only [hiddenCost,hv]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    rw [sum_comm]
    apply sum_congr rfl
    intro ω _
    rw [mul_sum]
  rw [he]
  convert h using 1
  simp only [integral,RankTracking.average,PilotEdits.average,mul_sum]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro ω _
  change (4:ℝ)*(D.weight ω*_)=D.weight ω*(4*_)
  ring

theorem actual_movement (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (H : ℕ) :
    movement (TreeCountData.data D (map A D hk z)) (by omega) H (weight A)≤
      8*(10:ℝ)^63*EpochAlpha.ell k*
        integral (TreeCountData.data D (map A D hk z)) H (coordinateCost A D hk z)+
      2*(10:ℝ)^63*EpochAlpha.ell k*allowance (shape A k J) k (weight A) := by
  have h := global_movement (TreeCountData.data D (map A D hk z)) (by omega) H (weight A)
    (fun v => radius_nonneg A _) (weight_separated A)
  have hc := mul_le_mul_of_nonneg_left (hidden_bound A D hk z H)
    (show 0≤2*(10:ℝ)^63*EpochAlpha.ell k by
      have := EpochAlpha.ell_one k; positivity)
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
