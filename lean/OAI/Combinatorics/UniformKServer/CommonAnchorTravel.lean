import Mathlib
import OAI.Combinatorics.UniformKServer.LevelAnchorContinuity

namespace OAI

                                         
section

/-! The diagonal term of tree matching is genuine retained heavy-anchor travel.
No claim is made about an unsupported prefix. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def actualAllocation (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :=
  TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω

theorem park_witness (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J))
    (hp : 0<park (shape A k J) (actualAllocation A D hk z t ω).amount v) :
    (region A D hk z t ω v).Nonempty := by
  apply witness A D hk z t ω v
  have hs := sum_nonneg (fun i (_ : i∈(univ : Finset (Children (shape A k J) v)))=>
    TreeAllocator.nonneg (TreeCountData.data D (map A D hk z)) (by omega) t ω i.val)
  change 0<TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω v-
    ∑ i : Children (shape A k J) v,TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω i.val at hp
  linarith

def labelTravel (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) : Label X A.C k→ℝ
  | Sum.inl l => if retainedMoving A D hk z j l t ω then
      dist ((heavyState A D hk z j t ω).center l) ((heavyState A D hk z j (t+1) ω).center l) else 0
  | Sum.inr _ => 0

theorem labelTravel_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (l : Label X A.C k) :
    0≤labelTravel A D hk z j t ω l := by
  cases l <;> simp only [labelTravel]
  · split_ifs <;> first | exact dist_nonneg | exact le_rfl
  · exact le_rfl

theorem common_label_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (j : Fin J) (l : Label X A.C k)
    (v : Vertex (size A k J)) (hv : v∈labelVertices A j l) :
    commonDistance (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)
      (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) v≤labelTravel A D hk z j t ω l := by
  unfold commonDistance
  split_ifs with hp
  · obtain ⟨p,hp'⟩ := park_witness A D hk z t ω v hp.1
    obtain ⟨q,hq'⟩ := park_witness A D hk z (t+1) ω v hp.2
    obtain ⟨_,hd,hl⟩ := mem_filter.mp hv
    have h0 : v≠0 := by intro he; subst v; rw [depth_root] at hd; omega
    have ho := last_region A D hk z t ω v h0 p hp'
    have hn := last_region A D hk z (t+1) ω v h0 q hq'
    have hi : (⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v h0; omega⟩ : Fin J)=j := by
      apply Fin.ext; change depth (shape A k J) v-1=j.val; omega
    rw [hi,hl] at ho hn
    rw [label_anchor A D hk z j l t ω v hv,label_anchor A D hk z j l (t+1) ω v hv]
    obtain he|⟨a,rfl,ha,hb⟩ := LevelMap.Data.supported_transition
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p q l ho.symm hn.symm
    · rw [he,dist_self]
      exact labelTravel_nonneg A D hk z j t ω l
    · change dist ((heavyState A D hk z j t ω).center a)
        ((heavyState A D hk z j (t+1) ω).center a)≤_
      by_cases he : (heavyState A D hk z j t ω).center a=(heavyState A D hk z j (t+1) ω).center a
      · rw [he,dist_self]; exact labelTravel_nonneg A D hk z j t ω (Sum.inl a)
      · change _ ≤ (if retainedMoving A D hk z j a t ω then _ else _)
        rw [ite_eq_left ⟨ha,hb,he⟩]
  · exact labelTravel_nonneg A D hk z j t ω l

omit [MetricSpace X] in
theorem all_label_sum (A : ActualPartitions.Config X) (f : Vertex (size A k J)→ℝ) (h0 : f 0=0) :
    (∑ j : Fin J,∑ l : Label X A.C k,∑ v∈labelVertices A j l,f v)=∑ v,f v := by
  simp_rw [label_fiber_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  by_cases hv : v=0
  · subst v
    simp only [h0,ite_self,sum_const_zero]
  · have hp := depth_positive A v hv
    have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v
    let j : Fin J := ⟨depth (shape A k J) v-1,by omega⟩
    have hd : depth (shape A k J) v=j.val+1 := by dsimp [j]; omega
    calc
      _ = (if depth (shape A k J) v=j.val+1 then f v else 0) := by
        apply sum_eq_single j
        · intro i _ hi
          have hn : depth (shape A k J) v≠i.val+1 := by
            intro he; apply hi; apply Fin.ext; dsimp [j]; omega
          rw [ite_eq_right hn]
        · intro hj; exact (hj (mem_univ _)).elim
      _ = _ := ite_eq_left hd

theorem common_travel_le (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ v,park (shape A k J) (actualAllocation A D hk z (t+1) ω).amount v*
      commonDistance (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)
        (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) v)≤anchorTravel A D hk z t ω := by
  rw [←all_label_sum A _ (by simp [commonDistance,anchor,dist_self])]
  have he : anchorTravel A D hk z t ω=∑ j : Fin J,∑ l : Label X A.C k,
      labelPark A D hk z j l (t+1) ω*labelTravel A D hk z j t ω l := by
    simp only [anchorTravel,Fintype.sum_sum_type,labelTravel,mul_ite,mul_zero,sum_const_zero,add_zero]
  rw [he]
  apply sum_le_sum
  intro j _
  apply sum_le_sum
  intro l _
  change _≤(∑ v∈labelVertices A j l,park _ (actualAllocation A D hk z (t+1) ω).amount v)*_
  rw [sum_mul]
  exact sum_le_sum fun v hv=>mul_le_mul_of_nonneg_left (common_label_bound A D hk z t ω j l v hv)
    ((actualAllocation A D hk z (t+1) ω).park_nonneg v)

end UniformKServer.PartitionTree

end


end

end OAI
