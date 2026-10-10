import Mathlib
import OAI.Combinatorics.UniformKServer.ActualSizeBudget
import OAI.Combinatorics.UniformKServer.AnchorLedger

namespace OAI

                                   
section

/-! Telescoping the actual retained-anchor potential, retaining the literal
allocation and true key-coordinate costs until the final financing step. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem variation_integral (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) :
    (∑ t∈range H,average D.weight (fun ω=>variation (weight A)
      (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω)
      (TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) (t+1) ω)))=
    TreeAllocationMovement.movement (TreeCountData.data D (map A D hk z)) (by omega) H (weight A) := by
  let d := TreeCountData.data D (map A D hk z)
  change integral d H (fun t ω=>variation (weight A) (TreeAllocator.allocation d (by omega) t ω)
    (TreeAllocator.allocation d (by omega) (t+1) ω))=_
  simp only [variation]
  rw [integral_sum]
  apply sum_congr rfl
  intro v _
  by_cases hv : v=0
  · simp only [hv,ite_true,integral,RankTracking.average,mul_zero,sum_const_zero]
  · simp only [ite_eq_right hv,nodeMove,integral,RankTracking.average,mul_sum]
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro ω _
    dsimp only [TreeAllocator.allocation,d]
    ring

theorem refresh_integral (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) :
    (∑ t∈range H,average D.weight (refreshStep A D hk z t))=sizeRefresh A D hk z H :=
  (weighted_integral (fun j : Fin J=>GeometricMass.radius A.R A.q j.val) D.weight H
    (fun j l t ω=>KeySizeTracker.charge (labelTracker A D hk z j l) t ω)).symm

theorem park_change_integral (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) :
    (∑ t∈range H,average D.weight (heavyParkChange A D hk z t)) ≤
    (1+1/22)*TreeAllocationMovement.movement (TreeCountData.data D (map A D hk z)) (by omega) H (weight A) := by
  have h := sum_le_sum (s:=range H) (fun t _=>PilotEdits.average_mono D.weight _ _
    (fun ω=>(D.positive ω).le) (heavy_park_variation A D hk z t))
  simp only [average_smul,←mul_sum,variation_integral] at h
  exact h

def payments (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) : ℝ := ∑ t∈range H,average D.weight (anchorPayments A D hk z t)

theorem payment_budget (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    payments A D hk z N ≤
      ((6/5)*132)*A.q*integral (TreeCountData.data D (map A D hk z)) N (coordinateCost A D hk z)+
      (driftLog k/3)*(∑ t∈range N,average D.weight (fun ω=>dist (D.position t ω (D.chosen t ω)) (D.request t ω)))+
      ((6/5)*132)*sizeRefresh A D hk z N+
      (12/5)*(1+1/22)*TreeAllocationMovement.movement (TreeCountData.data D (map A D hk z)) (by omega) N (weight A)+
      (6/5)*A.R*k := by
  have hs (t : ℕ) (ht : t∈range N) := PilotEdits.average_mono D.weight _ _
    (fun ω=>(D.positive ω).le) (fun ω=>anchor_step A D hk z t (mem_range.mp ht) ω hdiam)
  have ht := sum_le_sum hs
  simp only [average_add,average_sub,average_smul,sum_add_distrib,←mul_sum] at ht
  have htel := sum_range_sub (fun t=>average D.weight (frozenPotential A D hk z t t)) N
  rw [htel,refresh_integral] at ht
  have hd := sum_le_sum (s:=range N) (fun t _=>expected_drift A D hk z t hdiam)
  simp only [average_add,average_sub,average_smul,←mul_sum,sum_add_distrib] at hd
  have hp := park_change_integral A D hk z N
  have hzero : 0 ≤ average D.weight (fun ω=>frozenPotential A D hk z N N ω) :=
    sum_nonneg fun ω _=>mul_nonneg (D.positive ω).le (frozen_nonneg A D hk z N N ω)
  have hinit : average D.weight (fun ω=>frozenPotential A D hk z 0 0 ω) ≤ (6/5)*A.R*k := by
    have h := PilotEdits.average_mono D.weight _ _ (fun ω=>(D.positive ω).le) (frozen_bound A D hk z 0)
    simpa only [average,←sum_mul,D.total,one_mul] using h
  dsimp only [payments,integral,TreeCountData.data] at *
  change (average D.weight (fun ω=>frozenPotential A D hk z N N ω)-
    average D.weight (fun ω=>frozenPotential A D hk z 0 0 ω))+_ ≤ _ at ht
  simp only [average,RankTracking.average] at ht hd hp hzero hinit ⊢
  nlinarith only [ht,hd,hp,hzero,hinit]

end UniformKServer.PartitionTree

end


end

end OAI
