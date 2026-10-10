import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyKeyGeometry
import OAI.Combinatorics.UniformKServer.LabelParks
import OAI.Combinatorics.UniformKServer.ParkScale

namespace OAI

                                      
section

/-! The actual held heavy-key denominator and nearby-park geometry. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem ball_mass (μ : X→ℝ) (y : X) (r : ℝ) :
    ParkCapacity.mass μ (ParkCapacity.ball y r)=GeometricMass.mass μ y r := by
  simp only [ParkCapacity.mass,ParkCapacity.ball,sum_filter,GeometricMass.mass]

def heavyState (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) :=
  ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.heavyState (z j).1 t

def nearHeavy (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (y : X) (l : LevelMap.HeavySlot X) : Prop :=
  l∈(heavyState A D hk z j t ω).present ∧
    dist y ((heavyState A D hk z j t ω).center l)≤7*GeometricMass.radius A.R A.q j.val

theorem label_individual (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    labelPark A D hk z j l t ω/KeySizeTracker.held (labelTracker A D hk z j l) t ω≤(6/5)*132 := by
  have hc := (KeySizeTracker.comparisons (labelTracker A D hk z j l) t ω).1
  have hd := label_domination A D hk z j l t ω hdiam
  rw [labelTracker_size] at hc
  have hp : 0<KeySizeTracker.held (labelTracker A D hk z j l) t ω := by
    linarith [(KeySizeTracker.held_range (labelTracker A D hk z j l) t ω).1]
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem heavy_inner_subset (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (y : X) (l : LevelMap.HeavySlot X)
    (hl : nearHeavy A D hk z j t ω y l) :
    ParkCapacity.ball y (GeometricMass.radius A.R A.q j.val)⊆keyRegion A D hk z j (Sum.inl l) t ω := by
  intro p hp
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  exact LevelMap.Data.inner_heavy ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t y p l hl.1 hl.2 (mem_filter.mp hp).2

theorem heavy_denominator (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (y : X) (l : LevelMap.HeavySlot X)
    (hl : nearHeavy A D hk z j t ω y l) :
    ParkCoefficients.inner (HiddenFlow.current D t ω) y A.R A.q j.val≤
      (6/5)*KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) t ω := by
  have hm : ParkCapacity.mass (HiddenFlow.current D t ω)
      (ParkCapacity.ball y (GeometricMass.radius A.R A.q j.val))≤
      ParkCapacity.mass (HiddenFlow.current D t ω) (keyRegion A D hk z j (Sum.inl l) t ω) :=
    sum_le_sum_of_subset_of_nonneg (heavy_inner_subset A D hk z j t ω y l hl)
      (fun p _ _=>(HiddenFlow.flow D).post_nonneg t ω p)
  have hc := (KeySizeTracker.comparisons (labelTracker A D hk z j (Sum.inl l)) t ω).1
  rw [labelTracker_size] at hc
  change 1+GeometricMass.mass (HiddenFlow.current D t ω) y _≤_
  rw [ball_mass] at hm
  linarith

theorem label_anchor (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω)
    (v : Vertex (size A k J)) (hv : v∈labelVertices A j l) :
    anchor A D hk z t ω v=
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.anchor (z j) t l := by
  obtain ⟨_,hd,hl⟩ := mem_filter.mp hv
  have h0 : v≠0 := by intro he; subst v; rw [depth_root] at hd; omega
  rw [anchor,dite_eq_right h0]
  have hi : (⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v h0; omega⟩ : Fin J)=j := by
    apply Fin.ext
    change depth (shape A k J) v-1=j.val
    omega
  exact congrArg₂ (fun (i : Fin J) (a : Label X A.C k)=>
    ((A.input (N:=N) (J:=J) D hk ω).level i.val).data.anchor (z i) t a) hi hl

theorem near_park_witness (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (y : X) (l : LevelMap.HeavySlot X)
    (hl : nearHeavy A D hk z j t ω y l) (v : Vertex (size A k J))
    (hv : v∈labelVertices A j (Sum.inl l))
    (hp : 0<park (shape A k J) (TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω) v) :
    ∃ p∈region A D hk z t ω v,dist y p≤27*radius A (j.val+1) := by
  have ha : 0<TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω v := by
    unfold park at hp
    have hs := sum_nonneg (fun i (_ : i∈(univ : Finset (Children (shape A k J) v)))=>
      TreeAllocator.nonneg (TreeCountData.data D (map A D hk z)) (by omega) t ω i.val)
    linarith
  obtain ⟨p,hp⟩ := witness A D hk z t ω v ha
  have hd := (mem_filter.mp hv).2.1
  have h0 : v≠0 := by intro he; subst v; rw [depth_root] at hd; omega
  have hpdist := anchor_distance A D hk z t ω v h0 p hp
  rw [label_anchor A D hk z j (Sum.inl l) t ω v hv,hd] at hpdist
  have htri := dist_triangle y ((heavyState A D hk z j t ω).center l) p
  rw [dist_comm ((heavyState A D hk z j t ω).center l) p] at htri
  refine ⟨p,hp,?_⟩
  have hnear : dist y ((heavyState A D hk z j t ω).center l)≤7*radius A (j.val+1) := hl.2
  change dist p ((heavyState A D hk z j t ω).center l)≤_ at hpdist
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
