import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionTree

namespace OAI

                                        
section

/-! Actual prefix region geometry and the shared parked subtree capacity. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def radius (A : ActualPartitions.Config X) (d : ℕ) : ℝ := A.R*A.q^d

omit [Fintype X] [MetricSpace X] in
theorem radius_nonneg (A : ActualPartitions.Config X) (d : ℕ) : 0≤radius A d :=
  mul_nonneg A.R_pos.le (pow_nonneg A.q_pos.le _)

omit [Fintype X] [MetricSpace X] in
theorem radius_antitone (A : ActualPartitions.Config X) : Antitone (radius A) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one A.q_pos.le (by linarith [A.q_small]) hij) A.R_pos.le

omit [MetricSpace X] in
theorem depth_positive (A : ActualPartitions.Config X) (v : Vertex (size A k J)) (hv : v≠0) :
    0<depth (shape A k J) v := by rw [depth_child v hv]; omega

theorem disjoint (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (u v : Vertex (size A k J))
    (hd : depth (shape A k J) u=depth (shape A k J) v) (hne : u≠v) :
    Disjoint (region A D hk z t ω u) (region A D hk z t ω v) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hne (same_ancestor (mem_filter.mp hp).2 (mem_filter.mp hq).2 hd)

theorem diameter (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J))
    (hdiam : ∀ p q : X, dist p q≤40*A.R) (p q : X)
    (hp : p∈region A D hk z t ω v) (hq : q∈region A D hk z t ω v) :
    dist p q≤40*radius A (depth (shape A k J) v) := by
  by_cases hv : v=0
  · subst v
    simpa only [depth_root,radius,pow_zero,mul_one] using hdiam p q
  · have hd := depth_positive A v hv
    have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v
    let j : Fin J := ⟨depth (shape A k J) v-1,by omega⟩
    have he := same_prefix A D hk z t ω v p q hp hq j (by dsimp [j]; omega)
    have h := LevelMap.Data.diameter ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p q he
    change dist p q≤40*(A.R*A.q^(j.val+1)) at h
    have hj : j.val+1=depth (shape A k J) v := by dsimp [j]; omega
    simpa only [hj,radius] using h

def geometry (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hdiam : ∀ p q : X, dist p q≤40*A.R) :
    ParkCapacity.Geometry (shape A k J) X where
  region := region A D hk z t ω
  nested := nested A D hk z t ω
  disjoint := disjoint A D hk z t ω
  radius := radius A
  nonneg := radius_nonneg A
  antitone := radius_antitone A
  diameter := fun v p hp q hq => diameter A D hk z t ω v hdiam p q hp hq

theorem capacity (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hdiam : ∀ p q : X, dist p q≤40*A.R)
    (T : Finset (Vertex (size A k J))) (j : ℕ) (y : X)
    (hj : ∀ v∈T, j≤depth (shape A k J) v)
    (hw : ∀ v∈T, ∃ p∈region A D hk z t ω v, dist y p≤27*radius A (depth (shape A k J) v)) :
    (∑ v∈T, TreeRounding.park (shape A k J)
      (TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω) v)≤
      132*ParkCapacity.mass (HiddenFlow.current D t ω) (ParkCapacity.ball y (67*radius A j)) := by
  exact ParkCapacity.cumulative (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω)
    (geometry A D hk z t ω hdiam) (HiddenFlow.current D t ω)
    ((HiddenFlow.flow D).post_nonneg t ω) 132 (by norm_num)
    (TreePosteriorRegions.domination D (map A D hk z) (by omega) t ω) T j y hj hw

end UniformKServer.PartitionTree

end


end

end OAI
