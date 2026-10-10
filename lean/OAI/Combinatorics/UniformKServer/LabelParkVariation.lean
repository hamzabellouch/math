import Mathlib
import OAI.Combinatorics.UniformKServer.LabelParks
import OAI.Combinatorics.UniformKServer.PartitionMovement

namespace OAI

                                         
section

/-! Disjoint fixed-label fibers charge all grouped park variation to the literal
common-tree allocation, without a height factor. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

omit [MetricSpace X] in
theorem label_fiber_sum (A : ActualPartitions.Config X) (f : Vertex (size A k J)→ℝ) (j : Fin J) :
    (∑ l : Label X A.C k, ∑ v∈labelVertices A j l,f v)=
      ∑ v,if depth (shape A k J) v=j.val+1 then f v else 0 := by
  simp only [labelVertices,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  by_cases hd : depth (shape A k J) v=j.val+1
  · simp only [hd,true_and,ite_true,sum_ite_eq,mem_univ]
  · simp only [hd,false_and,ite_false,sum_const_zero]

omit [MetricSpace X] in
theorem weighted_label_sum (A : ActualPartitions.Config X) (f : Vertex (size A k J)→ℝ) :
    (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
      ∑ v∈labelVertices A j l,f v)=∑ v,if v=0 then 0 else weight A v*f v := by
  simp_rw [label_fiber_sum]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  by_cases hv : v=0
  · subst v
    simp only [depth_root,mul_ite,mul_zero]
    have he (j : Fin J) : ¬(0=j.val+1) := by omega
    simp only [he,ite_false,sum_const_zero,ite_true]
  · rw [ite_eq_right hv]
    have hp := depth_positive A v hv
    have hb : depth (shape A k J) v ≤ J := PrefixTree.depth_bound v
    let j : Fin J := ⟨depth (shape A k J) v-1,by omega⟩
    calc
      _ = GeometricMass.radius A.R A.q j.val*
        (if depth (shape A k J) v=j.val+1 then f v else 0) := by
          apply sum_eq_single j
          · intro i _ hi
            have hne : depth (shape A k J) v≠i.val+1 := by
              intro he
              apply hi
              apply Fin.ext
              dsimp [j]
              omega
            rw [ite_eq_right hne,mul_zero]
          · intro hj; exact (hj (mem_univ _)).elim
      _ = _ := by
        have hd : depth (shape A k J) v=j.val+1 := by dsimp [j]; omega
        rw [ite_eq_left hd]
        have hr : GeometricMass.radius A.R A.q j.val=weight A v := by
          dsimp only [weight,radius,GeometricMass.radius]
          rw [hd]
        rw [hr]

theorem label_park_variation (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
      |labelPark A D hk z j l (t+1) ω-labelPark A D hk z j l t ω|) ≤
      (1+1/22)*variation (weight A)
        (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω)
        (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) (t+1) ω) := by
  let a := TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω
  let b := TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) (t+1) ω
  have he : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
      |labelPark A D hk z j l (t+1) ω-labelPark A D hk z j l t ω|) ≤
      ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
        ∑ v∈labelVertices A j l,|park (shape A k J) b.amount v-park (shape A k J) a.amount v| := by
    apply sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    apply sum_le_sum
    intro l _
    unfold labelPark
    rw [←sum_sub_distrib]
    exact abs_sum_le_sum_abs _ _
  rw [weighted_label_sum] at he
  refine he.trans ((sum_le_sum fun v _=>?_).trans
    (TreeParking.weighted_variation a b (weight A) 22 (fun v=>radius_nonneg A _) (by norm_num) (weight_separated A)))
  by_cases hv : v=0
  · rw [ite_eq_left hv]
    exact mul_nonneg (radius_nonneg A _) (abs_nonneg _)
  · rw [ite_eq_right hv]

theorem heavy_park_variation (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
      |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω|) ≤
      (1+1/22)*variation (weight A)
        (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω)
        (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) (t+1) ω) := by
  refine le_trans (sum_le_sum fun j _=>mul_le_mul_of_nonneg_left ?_
    (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le) (label_park_variation A D hk z t ω)
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (sum_nonneg fun l _=>abs_nonneg _)

end UniformKServer.PartitionTree

end


end

end OAI
