import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionAnchors
import OAI.Combinatorics.UniformKServer.HiddenRegion
import OAI.Combinatorics.UniformKServer.KeySizePosterior

namespace OAI

                                 
section

/-! Actual fixed-coordinate parks and true posterior sizes of each level key. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def labelVertices (A : ActualPartitions.Config X) (j : Fin J) (l : Label X A.C k) :
    Finset (Vertex (size A k J)) :=
  univ.filter (fun v=>depth (shape A k J) v=j.val+1 ∧ lastLabel A v=l)

def keyRegion (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) : Finset X :=
  univ.filter (fun p=>word A D hk z t ω p j=l)

def labelPark (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ v∈labelVertices A j l,park (shape A k J)
    (TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω) v

def labelTracker (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) : KeySizeTracker.Input Ω (k+1) :=
  KeySizePosterior.input D (HiddenFlow.regionCount D (keyRegion A D hk z j l))
    (HiddenFlow.regionCount_range D _)

theorem keyRegion_measurable (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω v : Ω)
    (h : (D.filtration t).r ω v) : keyRegion A D hk z j l t ω=keyRegion A D hk z j l t v := by
  apply filter_congr
  intro p _
  have he : word A D hk z t ω p j=word A D hk z t v p j :=
    A.key_measurable (N:=N) (J:=J) D hk ω v t j.val h (z j) p
  rw [he]

theorem labelTracker_size (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) :
    (labelTracker A D hk z j l).size t ω=
      1+ParkCapacity.mass (HiddenFlow.current D t ω) (keyRegion A D hk z j l t ω) := by
  exact congrArg (fun x : ℝ=>1+x)
    (HiddenFlow.region_posterior D _ (keyRegion_measurable A D hk z j l) t ω)

theorem labelPark_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) :
    0≤labelPark A D hk z j l t ω :=
  sum_nonneg (fun v _=>(TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω).park_nonneg v)

theorem label_region (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω)
    (v : Vertex (size A k J)) (hv : v∈labelVertices A j l) :
    region A D hk z t ω v⊆keyRegion A D hk z j l t ω := by
  obtain ⟨_,hd,hl⟩ := mem_filter.mp hv
  have h0 : v≠0 := by intro he; subst v; rw [depth_root] at hd; omega
  intro p hp
  have h := last_region A D hk z t ω v h0 p hp
  have hi : (⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v h0; omega⟩ : Fin J)=j := by
    apply Fin.ext
    change depth (shape A k J) v-1=j.val
    omega
  rw [hi,hl] at h
  exact mem_filter.mpr ⟨mem_univ _,h.symm⟩

theorem label_domination (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    labelPark A D hk z j l t ω≤
      132*ParkCapacity.mass (HiddenFlow.current D t ω) (keyRegion A D hk z j l t ω) := by
  let d := TreeCountData.data D (map A D hk z)
  have hp (v : Vertex (size A k J)) : park (shape A k J) (TreeAllocator.amount d (by omega) t ω) v≤
      TreeAllocator.amount d (by omega) t ω v := by
    unfold park
    exact sub_le_self _ (sum_nonneg (fun i _=>TreeAllocator.nonneg d (by omega) t ω i.val))
  have hd := ParkCapacity.disjoint_mass (HiddenFlow.current D t ω) ((HiddenFlow.flow D).post_nonneg t ω)
    (geometry A D hk z t ω hdiam) (labelVertices A j l) (j.val+1) (keyRegion A D hk z j l t ω)
    (fun v hv=>(mem_filter.mp hv).2.1) (label_region A D hk z j l t ω)
  calc
    _≤∑ v∈labelVertices A j l,TreeAllocator.amount d (by omega) t ω v := sum_le_sum (fun v _=>hp v)
    _≤∑ v∈labelVertices A j l,132*ParkCapacity.mass (HiddenFlow.current D t ω) (region A D hk z t ω v) :=
      sum_le_sum (fun v _=>TreePosteriorRegions.domination D (map A D hk z) (by omega) t ω v)
    _=132*(∑ v∈labelVertices A j l,ParkCapacity.mass (HiddenFlow.current D t ω) (region A D hk z t ω v)) := (mul_sum ..).symm
    _≤_ := mul_le_mul_of_nonneg_left hd (by norm_num)

theorem labelPark_measurable (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω v : Ω)
    (h : (D.filtration t).r ω v) : labelPark A D hk z j l t ω=labelPark A D hk z j l t v := by
  apply sum_congr rfl
  intro u _
  unfold park
  rw [TreeAllocator.measurable _ _ _ h]
  congr 1
  apply sum_congr rfl
  intro i _
  exact TreeAllocator.measurable _ _ _ h _

end UniformKServer.PartitionTree

end


end

end OAI
