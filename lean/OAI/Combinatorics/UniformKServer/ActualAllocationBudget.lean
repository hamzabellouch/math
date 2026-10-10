import Mathlib
import OAI.Combinatorics.UniformKServer.ActualCoordinateBudget

namespace OAI

noncomputable section

/-! The concrete common-tree allocator paid by true metric movement. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixAB (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAB : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

theorem expect_average {Z : Type*} [Fintype Z] (P : Law Z) (w : Ω→ℝ) (f : Z→Ω→ℝ) :
    P.expect (fun z=>average w (f z))=average w (fun ω=>P.expect (fun z=>f z ω)) := by
  unfold Law.expect average
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  apply sum_congr rfl
  intro z _
  ring

theorem allocation_finance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) :
    (tapeLaw A N k J).expect (fun z=>movement (TreeCountData.data D (map A D hk z))
      (by omega) N (weight A))≤
    (8*(10:ℝ)^63/A.q)*(A.editBound+separationRate A)*EpochAlpha.ell k*(1+Real.log (k+1))*
      (∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
    (8*(10:ℝ)^63/A.q)*EpochAlpha.ell k*A.editEndpoint k J+
    2*(10:ℝ)^63*EpochAlpha.ell k*allowance (shape A k J) k (weight A) := by
  have h := (tapeLaw A N k J).expect_mono _ _ (fun z=>actual_movement A D hk z N)
  rw [Law.expect_add,Law.expect_const,Law.expect_mul] at h
  have he : (tapeLaw A N k J).expect
      (fun z=>integral (TreeCountData.data D (map A D hk z)) N (coordinateCost A D hk z))=
      totalCoordinate (N:=N) (J:=J) A D hk := by
    change (tapeLaw A N k J).expect (fun z=>∑ t∈range N,average D.weight (coordinateCost A D hk z t))=_
    rw [Law.expect_sum]
    exact sum_congr rfl (fun t _=>expect_average _ _ _)
  rw [he] at h
  have hc := coordinate_finance (N:=N) (J:=J) A D hk
  have hq := A.q_pos
  have hx : 0≤8*(10:ℝ)^63/A.q*EpochAlpha.ell k := by
    have := EpochAlpha.ell_one k
    positivity
  have hm := mul_le_mul_of_nonneg_left hc hx
  have hf : (8*(10:ℝ)^63/A.q*EpochAlpha.ell k)*
      (A.q*totalCoordinate (N:=N) (J:=J) A D hk)=
      8*(10:ℝ)^63*EpochAlpha.ell k*totalCoordinate (N:=N) (J:=J) A D hk := by
    field_simp [ne_of_gt hq]
  rw [hf] at hm
  nlinarith only [h,hm]

end UniformKServer.PartitionTree

end

end OAI
