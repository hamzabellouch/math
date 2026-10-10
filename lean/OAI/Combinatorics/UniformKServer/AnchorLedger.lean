import Mathlib
import OAI.Combinatorics.UniformKServer.ActualAnchorStep
import OAI.Combinatorics.UniformKServer.ActualAnchorFiltering
import OAI.Combinatorics.UniformKServer.LabelParkVariation

namespace OAI

                                   
section

/-! The actual signed five-substep ledger summed over fixed persistent slots.
No event-restricted filtering or assumed travel bound is used. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def anchorPayments (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J, ∑ l : LevelMap.HeavySlot X, anchorPayment A D hk z j l t ω

def heavyParkChange (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
    |labelPark A D hk z j (Sum.inl l) (t+1) ω-labelPark A D hk z j (Sum.inl l) t ω|

def refreshStep (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
    KeySizeTracker.charge (labelTracker A D hk z j l) t ω

theorem sizeCharge_nonneg {K : ℝ} (I : KeySizeTracker.Input Ω K) (t : ℕ) (ω : Ω) :
    0 ≤ KeySizeTracker.charge I t ω := by
  unfold KeySizeTracker.charge
  split_ifs
  · exact le_rfl
  · linarith [(KeySizeTracker.held_range I t ω).1,(KeySizeTracker.held_range I (t+1) ω).1]

theorem anchor_step (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ht : t<N) (ω : Ω) (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    frozenPotential A D hk z (t+1) (t+1) ω-frozenPotential A D hk z t t ω+
      anchorPayments A D hk z t ω ≤
      (frozenPotential A D hk z t (t+1) ω-frozenPotential A D hk z t t ω)+
      ((6/5)*132)*refreshStep A D hk z t ω+(12/5)*heavyParkChange A D hk z t ω := by
  have h := sum_le_sum (s:=univ) (fun j (_ : j∈(univ : Finset (Fin J)))=>
    sum_le_sum (s:=univ) (fun l _=>anchor_slot_step A D hk z j l t ht ω hdiam))
  have hr : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
      KeySizeTracker.charge (labelTracker A D hk z j (Sum.inl l)) t ω) ≤ refreshStep A D hk z t ω := by
    apply sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
    rw [Fintype.sum_sum_type]
    exact le_add_of_nonneg_right (sum_nonneg fun l _=>sizeCharge_nonneg _ _ _)
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ (6/5:ℝ)*132 by norm_num)
  simp only [sum_add_distrib,sum_sub_distrib] at h
  dsimp only [frozenPotential,anchorPayments,heavyParkChange]
  simp only [mul_sum,mul_assoc,mul_comm] at h hm ⊢
  linarith only [h,hm]

theorem frozen_nonneg (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t s : ℕ) (ω : Ω) : 0 ≤ frozenPotential A D hk z t s ω :=
  sum_nonneg fun j _=>sum_nonneg fun l _=>anchorTerm_nonneg A D hk z j l t t s t ω

omit [MetricSpace X] in
theorem weighted_parks (A : ActualPartitions.Config X) (a : Allocation (shape A k J) k) :
    (∑ v,weight A v*park (shape A k J) a.amount v) ≤ A.R*k := by
  calc
    _ ≤ ∑ v,A.R*park (shape A k J) a.amount v := by
      apply sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_right _ (a.park_nonneg v)
      have h := radius_antitone A (show 0 ≤ depth (shape A k J) v from Nat.zero_le _)
      simpa only [weight,radius,pow_zero,mul_one] using h
    _ = _ := by rw [←mul_sum,TreeParking.total]

theorem frozen_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : frozenPotential A D hk z t t ω ≤ (6/5)*A.R*k := by
  let a := TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω
  have hb := sum_le_sum (s:=univ) (fun j (_ : j∈(univ : Finset (Fin J)))=>
    sum_le_sum (s:=univ) (fun l _=>anchorTerm_bound A D hk z j l t t t ω))
  have hh : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
      labelPark A D hk z j (Sum.inl l) t ω) ≤ ∑ v,weight A v*park (shape A k J) a.amount v := by
    have he : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : LevelMap.HeavySlot X,
        labelPark A D hk z j (Sum.inl l) t ω) ≤
        ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,labelPark A D hk z j l t ω := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le
      rw [Fintype.sum_sum_type]
      exact le_add_of_nonneg_right (sum_nonneg fun l _=>labelPark_nonneg A D hk z j _ t ω)
    unfold labelPark at he
    rw [weighted_label_sum] at he
    refine he.trans (sum_le_sum fun v _=>?_)
    by_cases hv : v=0
    · rw [ite_eq_left hv]
      exact mul_nonneg (radius_nonneg A _) (a.park_nonneg v)
    · rw [ite_eq_right hv]
      exact le_rfl
  have hm := mul_le_mul_of_nonneg_left (hh.trans (weighted_parks A a)) (show (0:ℝ) ≤ 6/5 by norm_num)
  change frozenPotential A D hk z t t ω ≤ _ at hb
  simp only [←mul_sum,mul_assoc] at hb hm
  linarith only [hb,hm]

end UniformKServer.PartitionTree

end


end

end OAI
