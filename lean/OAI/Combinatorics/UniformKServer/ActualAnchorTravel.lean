import Mathlib
import OAI.Combinatorics.UniformKServer.AnchorBudget

namespace OAI

                                         
section

/-! Literal metric movement of retained heavy anchors, weighted by the new
parked mass. This is the travel used when projecting rounded tree servers. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

theorem anchor_distance (D : LevelMap.Data X N H) (z : Tape D) (t : ℕ)
    (l : HeavySlot X) (ho : l∈(D.heavyState z.1 t).present)
    (hn : l∈(D.heavyState z.1 (t+1)).present)
    (hm : (D.heavyState z.1 t).center l≠(D.heavyState z.1 (t+1)).center l) :
    dist ((D.heavyState z.1 t).center l) ((D.heavyState z.1 (t+1)).center l) ≤ 40*D.r := by
  have h := HeavyProcess.moved_step (D.heavyState z.1 t)
    (HeavyProcess.runPair D.base D.positive.le (by simp [HeavySlot]) D.heavyFlag D.point
      (HeavyProcess.radiusStream D.r N z.1) (HeavyProcess.radiusStream_bounds D.r D.positive.le N z.1) t).1
    D.positive.le (by simp [HeavySlot]) (D.heavyFlag t) (D.point t)
    (HeavyProcess.radiusStream D.r N z.1 t) (HeavyProcess.radiusStream_bounds D.r D.positive.le N z.1 t)
    l ho hn hm
  have ha : (D.heavyState z.1 (t+1)).center l=D.point t := h.2.1
  rw [ha]
  exact h.2.2.2.1

end UniformKServer.LevelMap.Data
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def anchorTravel (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J, ∑ l : LevelMap.HeavySlot X,
    if retainedMoving A D hk z j l t ω then
      labelPark A D hk z j (Sum.inl l) (t+1) ω*
        dist ((heavyState A D hk z j t ω).center l) ((heavyState A D hk z j (t+1) ω).center l)
    else 0

theorem anchorTravel_le (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    anchorTravel A D hk z t ω ≤ 160*anchorPayments A D hk z t ω := by
  simp only [anchorTravel,anchorPayments,mul_sum]
  apply sum_le_sum
  intro j _
  apply sum_le_sum
  intro l _
  by_cases h : retainedMoving A D hk z j l t ω
  · rw [ite_eq_left h,anchorPayment,ite_eq_left h]
    have hd := LevelMap.Data.anchor_distance ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
      (z j) t l h.1 h.2.1 h.2.2
    have hm := mul_le_mul_of_nonneg_left hd (labelPark_nonneg A D hk z j (Sum.inl l) (t+1) ω)
    change labelPark A D hk z j (Sum.inl l) (t+1) ω*
      dist ((heavyState A D hk z j t ω).center l) ((heavyState A D hk z j (t+1) ω).center l)
        ≤ _*(40*GeometricMass.radius A.R A.q j.val) at hm
    nlinarith only [hm]
  · simp only [ite_eq_right h,anchorPayment,mul_zero]
    exact le_rfl

def totalAnchorTravel (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) : ℝ := ∑ t∈range H,average D.weight (anchorTravel A D hk z t)

theorem totalAnchorTravel_le (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (H : ℕ) : totalAnchorTravel A D hk z H ≤ 160*payments A D hk z H := by
  have h := sum_le_sum (s:=range H) (fun t _=>PilotEdits.average_mono D.weight _ _
    (fun ω=>(D.positive ω).le) (anchorTravel_le A D hk z t))
  simpa only [average_smul,←mul_sum,totalAnchorTravel,payments] using h

end UniformKServer.PartitionTree

end


end

end OAI
