import Mathlib
import OAI.Combinatorics.UniformKServer.ActualAnchorRelease
import OAI.Combinatorics.UniformKServer.ActualAnchorPotential

namespace OAI

                                       
section

/-! Complete per-slot anchor update, including deleted, newly born, unchanged,
and retained moving slots; then the faithful five-substep ledger. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def retainedMoving (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω) : Prop :=
  l∈(heavyState A D hk z j t ω).present ∧ l∈(heavyState A D hk z j (t+1) ω).present ∧
    (heavyState A D hk z j t ω).center l≠(heavyState A D hk z j (t+1) ω).center l

def anchorPayment (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ω : Ω) : ℝ :=
  if retainedMoving A D hk z j l t ω then (1/4)*GeometricMass.radius A.R A.q j.val*
    labelPark A D hk z j (Sum.inl l) (t+1) ω else 0

theorem parameter_anchors (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ht : t<N) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    anchorTerm A D hk z j l (t+1) (t+1) (t+1) (t+1) ω-
      anchorTerm A D hk z j l (t+1) (t+1) (t+1) t ω+anchorPayment A D hk z j l t ω ≤
      (6/5)*GeometricMass.radius A.R A.q j.val*
        |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω| := by
  have hfree : 0 ≤ (6/5)*GeometricMass.radius A.R A.q j.val*
        |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω| :=
    mul_nonneg (mul_nonneg (by norm_num) (GeometricMass.radius_pos _ _ A.R_pos A.q_pos _).le) (abs_nonneg _)
  by_cases hn : l∈(heavyState A D hk z j (t+1) ω).present
  · by_cases ho : l∈(heavyState A D hk z j t ω).present
    · by_cases hm : (heavyState A D hk z j t ω).center l=(heavyState A D hk z j (t+1) ω).center l
      · have he : anchorIntegral A D hk z j l (t+1) (t+1) ω=anchorIntegral A D hk z j l (t+1) t ω := by
          dsimp only [anchorIntegral]; rw [hm]
        simp only [anchorTerm,he,sub_self,anchorPayment,retainedMoving,hm,ne_eq,not_true_eq_false,and_false,ite_false,add_zero]
        exact hfree
      · have h := actual_anchor_release A D hk z j t ht ω l ho hn hm
        have he : anchorTerm A D hk z j l (t+1) (t+1) (t+1) (t+1) ω-
            anchorTerm A D hk z j l (t+1) (t+1) (t+1) t ω=
            GeometricMass.radius A.R A.q j.val*labelPark A D hk z j (Sum.inl l) (t+1) ω/
              KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) (t+1) ω*
              (∑ p∈keyRegion A D hk z j (Sum.inl l) (t+1) ω,HiddenFlow.current D (t+1) ω p*
                (AnchorRamp.value (GeometricMass.radius A.R A.q j.val) ((heavyState A D hk z j (t+1) ω).center l) p-
                 AnchorRamp.value (GeometricMass.radius A.R A.q j.val) ((heavyState A D hk z j t ω).center l) p)) := by
          simp only [anchorTerm,anchorIntegral,AnchorPotential.integral,mul_sub,sum_sub_distrib]
        rw [he,anchorPayment,ite_eq_left ⟨ho,hn,hm⟩]
        nlinarith only [h,hfree]
    · have hz := absent_park A D hk z j l t ω hdiam ho
      have hb := anchorTerm_bound A D hk z j l (t+1) (t+1) (t+1) ω
      have hp := anchorTerm_nonneg A D hk z j l (t+1) (t+1) (t+1) t ω
      rw [anchorPayment,ite_eq_right (by intro h; exact ho h.1),hz,sub_zero,
        abs_of_nonneg (labelPark_nonneg A D hk z j (Sum.inl l) (t+1) ω)]
      linarith
  · have hz := absent_park A D hk z j l (t+1) ω hdiam hn
    simp only [anchorTerm,hz,mul_zero,zero_div,zero_mul,sub_self,anchorPayment,retainedMoving,hn,false_and,and_false,ite_false,add_zero]
    simpa only [hz] using hfree

theorem anchor_slot_step (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (l : LevelMap.HeavySlot X) (t : ℕ) (ht : t<N) (ω : Ω)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    anchorTerm A D hk z j l (t+1) (t+1) (t+1) (t+1) ω-anchorTerm A D hk z j l t t t t ω+
      anchorPayment A D hk z j l t ω ≤
      (anchorTerm A D hk z j l t t (t+1) t ω-anchorTerm A D hk z j l t t t t ω)+
      GeometricMass.radius A.R A.q j.val*((6/5)*132)*KeySizeTracker.charge (labelTracker A D hk z j (Sum.inl l)) t ω+
      (12/5)*GeometricMass.radius A.R A.q j.val*
        |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω| := by
  have hf := parameter_reference A D hk z j l t ω hdiam
  have hp := (le_abs_self _).trans (parameter_parks A D hk z j l t ω)
  have ha := parameter_anchors A D hk z j l t ht ω hdiam
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
