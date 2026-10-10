import Mathlib
import OAI.Combinatorics.UniformKServer.LevelAnchorRelease
import OAI.Combinatorics.UniformKServer.HeavyLabelParks

namespace OAI

                                          
section

/-! Retained heavy-label release with the literal post-request law and held
size. The heavy test is extracted from the actual level input. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem actual_anchor_release (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ht : t<N) (ω : Ω) (l : LevelMap.HeavySlot X)
    (ho : l∈(heavyState A D hk z j t ω).present) (hn : l∈(heavyState A D hk z j (t+1) ω).present)
    (hm : (heavyState A D hk z j t ω).center l≠(heavyState A D hk z j (t+1) ω).center l) :
    GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) (t+1) ω/
      KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) (t+1) ω*
      (∑ p∈keyRegion A D hk z j (Sum.inl l) (t+1) ω,HiddenFlow.current D (t+1) ω p*
        (AnchorRamp.value (GeometricMass.radius A.R A.q j.val) ((heavyState A D hk z j (t+1) ω).center l) p-
         AnchorRamp.value (GeometricMass.radius A.R A.q j.val) ((heavyState A D hk z j t ω).center l) p))≤
       -(1/4)*GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) (t+1) ω := by
  let I := (A.input (N:=N) (J:=J) D hk ω).level j.val
  have hp : I.data.point t=D.request t ω := by
    dsimp only [LevelMap.Data.point]
    rw [dite_eq_left ht]
    rfl
  have hμ := (HiddenFlow.flow D).post_nonneg (t+1) ω
  have hr := GeometricMass.radius_pos A.R A.q A.R_pos A.q_pos j.val
  have hh : I.data.heavyFlag t→GeometricMass.mass (HiddenFlow.current D (t+1) ω) (I.data.point t)
      (51200*I.data.r)≤(1+A.P.deltaH)*GeometricMass.mass (HiddenFlow.current D (t+1) ω)
        (I.data.point t) (A.P.gammaH*I.data.r) := by
    intro hh
    obtain ⟨ht',hh⟩ := hh
    rw [hp]
    exact hh
  have hH : 1≤GeometricMass.mass (HiddenFlow.current D (t+1) ω) (I.data.point t) (A.P.gammaH*I.data.r) := by
    rw [hp]
    exact (HiddenFlow.serving_mass D t ω).trans (GeometricMass.mass_center _ hμ _ _ (mul_nonneg A.P.gammaH_pos.le hr.le))
  have hd := (KeySizeTracker.comparisons (labelTracker A D hk z j (Sum.inl l)) (t+1) ω).2
  rw [labelTracker_size] at hd
  exact LevelMap.Data.anchor_release I.data I.order (z j) t l ho hn hm
    (HiddenFlow.current D (t+1) ω) hμ A.P.gammaH A.P.deltaH
    (labelPark A D hk z j (Sum.inl l) (t+1) ω)
    (KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) (t+1) ω)
    (by linarith [A.P.gammaH_small]) (by linarith [A.P.deltaH_small])
    (labelPark_nonneg A D hk z j (Sum.inl l) (t+1) ω)
    (by have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) (t+1) ω).1; linarith)
    hH hh hd

end UniformKServer.PartitionTree

end


end

end OAI
