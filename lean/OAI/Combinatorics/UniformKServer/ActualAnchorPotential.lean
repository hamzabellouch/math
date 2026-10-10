import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyLabelParks
import OAI.Combinatorics.UniformKServer.AnchorPotential

namespace OAI

                                            
section

/-! The actual four parameter substeps after the unconditional hidden drift. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def anchorIntegral (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (m a : ℕ) (ω : Ω) : ℝ :=
  AnchorPotential.integral (GeometricMass.radius A.R A.q j.val) (HiddenFlow.current D m ω)
    (keyRegion A D hk z j (Sum.inl l) m ω) ((heavyState A D hk z j a ω).center l)

def anchorTerm (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (b u m a : ℕ) (ω : Ω) : ℝ :=
  GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) b ω/
    KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) u ω*anchorIntegral A D hk z j l m a ω

theorem anchorIntegral_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (m a : ℕ) (ω : Ω) :
    0 ≤ anchorIntegral A D hk z j l m a ω :=
  AnchorPotential.integral_nonneg _ _ ((HiddenFlow.flow D).post_nonneg m ω) _ _

theorem anchorIntegral_held (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (m a : ℕ) (ω : Ω) :
    anchorIntegral A D hk z j l m a ω ≤ (6/5)*KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) m ω := by
  have hi := AnchorPotential.integral_le (GeometricMass.radius A.R A.q j.val) _
    ((HiddenFlow.flow D).post_nonneg m ω) (keyRegion A D hk z j (Sum.inl l) m ω) ((heavyState A D hk z j a ω).center l)
  have hc := (KeySizeTracker.comparisons (labelTracker A D hk z j (Sum.inl l)) m ω).1
  rw [labelTracker_size] at hc
  exact hi.trans (by
    change (∑ p∈keyRegion A D hk z j (Sum.inl l) m ω,HiddenFlow.current D m ω p) ≤ _
    dsimp only [ParkCapacity.mass] at hc
    linarith)

theorem anchorTerm_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (b u m a : ℕ) (ω : Ω) :
    0 ≤ anchorTerm A D hk z j l b u m a ω := by
  unfold anchorTerm
  exact mul_nonneg (div_nonneg (mul_nonneg (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    (labelPark_nonneg A D hk z j (Sum.inl l) b ω)) (by have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) u ω).1; linarith))
    (anchorIntegral_nonneg A D hk z j l m a ω)

theorem absent_park (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) (hl : l∉(heavyState A D hk z j t ω).present) :
    labelPark A D hk z j (Sum.inl l) t ω=0 := by
  have he : keyRegion A D hk z j (Sum.inl l) t ω=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hc := (LevelMap.Data.key_heavy_iff ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p l).mp ((mem_filter.mp hp).2)
    exact hl hc.1
  have hd := label_domination A D hk z j (Sum.inl l) t ω hdiam
  rw [he,ParkCapacity.mass,sum_empty,mul_zero] at hd
  exact le_antisymm hd (labelPark_nonneg A D hk z j (Sum.inl l) t ω)

theorem anchorTerm_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (b m a : ℕ) (ω : Ω) :
    anchorTerm A D hk z j l b m m a ω ≤ 
      (6/5)*GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) b ω := by
  have hu : 0<KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) m ω := by
    have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) m ω).1; linarith
  have hi := (div_le_iff₀ hu).mpr (anchorIntegral_held A D hk z j l m a ω)
  have hm := mul_le_mul_of_nonneg_left hi (mul_nonneg (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    (labelPark_nonneg A D hk z j (Sum.inl l) b ω))
  dsimp only [anchorTerm]
  calc
    _ = GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) b ω*
        (anchorIntegral A D hk z j l m a ω/KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) m ω) := by ring
    _ ≤ _ := hm
    _ = _ := by ring

theorem parameter_reference (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    anchorTerm A D hk z j l t (t+1) (t+1) t ω-anchorTerm A D hk z j l t t (t+1) t ω ≤ 
      GeometricMass.radius A.R A.q j.val*((6/5)*132)*KeySizeTracker.charge (labelTracker A D hk z j (Sum.inl l)) t ω := by
  have hu : 0<KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) t ω := by
    have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) t ω).1; linarith
  exact AnchorPotential.reference (labelTracker A D hk z j (Sum.inl l)) _ _ _ _ _ t ω
    (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le (labelPark_nonneg A D hk z j (Sum.inl l) t ω)
    (anchorIntegral_nonneg A D hk z j l (t+1) t ω)
    (AnchorPotential.integral_le _ _ ((HiddenFlow.flow D).post_nonneg (t+1) ω) _ _)
    (labelTracker_size A D hk z j (Sum.inl l) (t+1) ω)
    ((div_le_iff₀ hu).mp (label_individual A D hk z j (Sum.inl l) t ω hdiam)) (by norm_num)

theorem parameter_parks (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω) :
    |anchorTerm A D hk z j l (t+1) (t+1) (t+1) t ω-anchorTerm A D hk z j l t (t+1) (t+1) t ω| ≤ 
      (6/5)*GeometricMass.radius A.R A.q j.val*
        |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω| := by
  exact AnchorScalar.parks _ _ _ _ _ _ (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    (anchorIntegral_nonneg A D hk z j l (t+1) t ω)
    (by have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) (t+1) ω).1; linarith)
    (anchorIntegral_held A D hk z j l (t+1) t ω)

end UniformKServer.PartitionTree

end


end

end OAI
