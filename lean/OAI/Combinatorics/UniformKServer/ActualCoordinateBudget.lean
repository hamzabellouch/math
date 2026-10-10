import Mathlib
import OAI.Combinatorics.UniformKServer.ActualEditIntegration
import OAI.Combinatorics.UniformKServer.ActualEditFinance

namespace OAI

noncomputable section

/-! The actual multiscale coordinate motion is height-free after integration. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixCB (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairCB : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

def separationRate (A : ActualPartitions.Config X) : ℝ :=
  8+(16*A.C+33)*(1+1/Real.log (1+A.P.deltaH))

omit [Fintype X] [MetricSpace X] in
theorem separationRate_nonneg (A : ActualPartitions.Config X) : 0 ≤ separationRate A := by
  have hδ : 0<Real.log (1+A.P.deltaH) := Real.log_pos (by linarith [A.P.deltaH_pos])
  have hC : 0≤16*A.C+33 := by linarith [A.C_one]
  unfold separationRate
  positivity

def totalCoordinate (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) : ℝ :=
  ∑ t∈range N,average D.weight (fun ω=>(tapeLaw A N k J).expect (fun z=>coordinateCost A D hk z t ω))

theorem average_move (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (n : Fin N) :
    average D.weight (fun ω=>(tapeLaw A N k J).expect (fun z=>pathMove A D hk z n.val ω))≤
       separationRate A*(1+Real.log k)*average D.weight (moverCost (HiddenFlow.flow D) n.val) := by
  have h := average_mono D.weight _ _ (fun ω=>(D.positive ω).le) (fun ω=>move_expect (J:=J) A D hk ω n)
  change _≤average D.weight (fun ω=>separationRate A*(1+Real.log k)*
    dist (D.request n.val ω) (D.position n.val ω (D.chosen n.val ω))) at h
  rw [average_smul] at h
  change _≤_*_*(∑ ω,D.weight ω*_) at h
  rw [←HiddenFlow.expected_mover_cost D n.val] at h
  exact h

theorem coordinate_step_budget (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (n : Fin N) :
    A.q*average D.weight (fun ω=>(tapeLaw A N k J).expect (fun z=>coordinateCost A D hk z n.val ω))≤
      average D.weight (A.keyEditCost (N:=N) (J:=J) D hk n.val)+
      separationRate A*(1+Real.log k)*average D.weight (moverCost (HiddenFlow.flow D) n.val) := by
  have h := average_mono D.weight _ _ (fun ω=>(D.positive ω).le) (fun ω=>
    (tapeLaw A N k J).expect_mono _ _ (fun z=>coordinate_split A D hk z n.val ω))
  simp only [Law.expect_mul,Law.expect_add,average_smul,average_add] at h
  rw [edits_expect] at h
  exact h.trans (add_le_add le_rfl (average_move A D hk n))

theorem coordinate_finance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) :
    A.q*totalCoordinate (N:=N) (J:=J) A D hk≤
      (A.editBound+separationRate A)*(1+Real.log (k+1))*
        (∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+A.editEndpoint k J := by
  let Q := ∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t)
  have hQ : 0≤Q := sum_nonneg (fun t _=>sum_nonneg (fun ω _=>mul_nonneg (D.positive ω).le
    (sum_nonneg (fun p _=>mul_nonneg ((HiddenFlow.flow D).mover_nonneg t ω p) dist_nonneg))))
  have h : (∑ t∈range N, A.q*average D.weight (fun ω=>(tapeLaw A N k J).expect
      (fun z=>coordinateCost A D hk z t ω)))≤
      ∑ t∈range N,(average D.weight (A.keyEditCost (N:=N) (J:=J) D hk t)+
        separationRate A*(1+Real.log k)*average D.weight (moverCost (HiddenFlow.flow D) t)) :=
    sum_le_sum (fun t ht=>coordinate_step_budget (J:=J) A D hk ⟨t,mem_range.mp ht⟩)
  simp only [sum_add_distrib,←mul_sum] at h
  change A.q*totalCoordinate (N:=N) (J:=J) A D hk≤
    (∑ t∈range N,average D.weight (A.keyEditCost (N:=N) (J:=J) D hk t))+
      separationRate A*(1+Real.log k)*Q at h
  have hf := A.edit_finance (N:=N) (J:=J) D hk
  have hlog : 1+Real.log k≤1+Real.log (k+1) := by
    have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    linarith [Real.log_le_log hk' (show (k:ℝ)≤k+1 by linarith)]
  have hz := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (separationRate_nonneg A)) hQ
  change _≤A.editBound*(1+Real.log (k+1))*Q+_ at hf
  change _≤(A.editBound+separationRate A)*(1+Real.log (k+1))*Q+_
  nlinarith only [h,hf,hz]

end UniformKServer.PartitionTree

end

end OAI
