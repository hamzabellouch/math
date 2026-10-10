import Mathlib
import OAI.Combinatorics.UniformKServer.LevelParkCapacity
import OAI.Combinatorics.UniformKServer.ParkPointwise
import OAI.Combinatorics.UniformKServer.HeavyLabelParks

namespace OAI

                                               
section

/-! Instantiate the height-free coefficient estimate with actual nearby heavy
slots of the completed fractional state. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def selectedVertices (A : ActualPartitions.Config X) (s : Fin J→Option (LevelMap.HeavySlot X))
    (i : ℕ) : Finset (Vertex (size A k J)) :=
  if hi : i<J then ((s ⟨i,hi⟩).map (fun l=>labelVertices A ⟨i,hi⟩ (Sum.inl l))).getD ∅ else ∅

def selectedDen (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (s : Fin J→Option (LevelMap.HeavySlot X)) (t : ℕ) (ω : Ω) (i : ℕ) : ℝ :=
  if hi : i<J then ((s ⟨i,hi⟩).map (fun l=>KeySizeTracker.held (labelTracker A D hk z ⟨i,hi⟩ (Sum.inl l)) t ω)).getD (k+1) else k+1

omit [MetricSpace X] in
theorem selected_depth (A : ActualPartitions.Config X) (s : Fin J→Option (LevelMap.HeavySlot X))
    (i : ℕ) (hi : i<J) (v : Vertex (size A k J)) (hv : v∈selectedVertices A s i) :
    depth (shape A k J) v=i+1 := by
  simp only [selectedVertices,dite_eq_left hi] at hv
  cases hs : s ⟨i,hi⟩ with
  | none => simp only [hs,Option.map_none,Option.getD_none,Finset.notMem_empty] at hv
  | some l =>
    simp only [hs,Option.map_some,Option.getD_some] at hv
    exact (mem_filter.mp hv).2.1

theorem selected_coefficients (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (s : Fin J→Option (LevelMap.HeavySlot X)) (t : ℕ) (ω : Ω) (y : X)
    (hs : ∀ j l,s j=some l→nearHeavy A D hk z j t ω y l)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    (∑ i∈range J,(∑ v∈selectedVertices A s i,park (shape A k J)
      (TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω) v)/selectedDen A D hk z s t ω i)≤
      (6/5)*132*(2+7/Real.log 2)*Real.log (k+1) := by
  let a := TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω
  let μ := HiddenFlow.current D t ω
  let b : ℕ→ℝ := fun i=>∑ v∈selectedVertices A s i,park (shape A k J) a.amount v
  have hm : ∀ p,0≤μ p := (HiddenFlow.flow D).post_nonneg t ω
  have htotal : ∑ p,μ p≤(k+1:ℝ)-1 := by
    have ht := (HiddenFlow.flow D).post_total t ω
    change (∑ p,μ p)=k at ht
    linarith
  have hden (i : ℕ) (hi : i<J) : ParkCoefficients.inner μ y A.R A.q i≤
      (6/5)*selectedDen A D hk z s t ω i := by
    simp only [selectedDen,dite_eq_left hi]
    cases he : s ⟨i,hi⟩ with
    | none =>
      simp only [Option.map_none,Option.getD_none]
      have hh := (GeometricMass.mass_total μ hm y (GeometricMass.radius A.R A.q i)).trans htotal
      unfold ParkCoefficients.inner
      linarith [Nat.cast_nonneg (α:=ℝ) k]
    | some l =>
      simp only [Option.map_some,Option.getD_some]
      exact heavy_denominator A D hk z ⟨i,hi⟩ t ω y l (hs _ _ he)
  have hind (i : ℕ) (hi : i<J) : b i/selectedDen A D hk z s t ω i≤(6/5)*132 := by
    dsimp only [b]
    simp only [selectedVertices,selectedDen,dite_eq_left hi]
    cases he : s ⟨i,hi⟩ with
    | none => simp only [Option.map_none,Option.getD_none,sum_empty,zero_div]; norm_num
    | some l =>
      simp only [Option.map_some,Option.getD_some]
      exact label_individual A D hk z ⟨i,hi⟩ (Sum.inl l) t ω hdiam
  have hcap (j : ℕ) (_hj : j<J) : ParkCoefficients.tail b J j≤132*(ParkCoefficients.outer μ y A.R A.q j-1) := by
    have h := ParkCapacity.level_cumulative a (geometry A D hk z t ω hdiam) μ hm 132 (by norm_num)
      (TreePosteriorRegions.domination D (map A D hk z) (by omega) t ω)
      (selectedVertices A s) J j y (selected_depth A s) (by
        intro i hi v hv hp
        simp only [selectedVertices,dite_eq_left hi] at hv
        cases he : s ⟨i,hi⟩ with
        | none => simp only [he,Option.map_none,Option.getD_none,Finset.notMem_empty] at hv
        | some l =>
          simp only [he,Option.map_some,Option.getD_some] at hv
          exact near_park_witness A D hk z ⟨i,hi⟩ t ω y l (hs _ _ he) v hv hp)
    simpa only [ParkCoefficients.outer,add_sub_cancel_left,geometry,radius,GeometricMass.radius,ball_mass] using h
  have hp : 67*A.q^7≤1 := by
    have hq := pow_le_pow_left₀ A.q_pos.le A.q_small 7
    norm_num at hq
    linarith
  exact ParkCoefficients.pointwise μ hm y (k+1) A.R A.q 132 (6/5) htotal A.R_pos A.q_pos
    (by norm_num) (by norm_num) 7 J hp b (selectedDen A D hk z s t ω)
    (fun i=>sum_nonneg (fun v _=>a.park_nonneg v)) hden hind hcap

end UniformKServer.PartitionTree

end


end

end OAI
