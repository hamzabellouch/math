import Mathlib
import OAI.Combinatorics.UniformKServer.ActualAnchorTravel
import OAI.Combinatorics.UniformKServer.ActualAllocationBudget

namespace OAI

noncomputable section

/-! Horizon-independent financing of literal retained-anchor metric travel.
All quantities here are expectations under the actual independent finite tape. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixAF (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAF : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

def allocationRate (A : ActualPartitions.Config X) (k : ℕ) : ℝ :=
  (8*(10:ℝ)^63/A.q)*(A.editBound+separationRate A)*EpochAlpha.ell k*(1+Real.log (k+1))
def allocationEndpoint (A : ActualPartitions.Config X) (k J : ℕ) : ℝ :=
  (8*(10:ℝ)^63/A.q)*EpochAlpha.ell k*A.editEndpoint k J+
    2*(10:ℝ)^63*EpochAlpha.ell k*allowance (shape A k J) k (weight A)
def anchorRate (A : ActualPartitions.Config X) (k : ℕ) : ℝ :=
  160*(((6/5)*132)*(1+288*KeySizeTracker.ell (k+1))*(A.editBound+separationRate A)*
    (1+Real.log (k+1))+driftLog k/3+(12/5)*(1+1/22)*allocationRate A k)
def anchorEndpoint (A : ActualPartitions.Config X) (k J : ℕ) : ℝ :=
  160*(((6/5)*132)*(1+288*KeySizeTracker.ell (k+1))*A.editEndpoint k J+
    ((6/5)*132)*sizeEndpoint A k J+(12/5)*(1+1/22)*allocationEndpoint A k J+(6/5)*A.R*k)

theorem coordinate_integral_expect (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k) :
    (tapeLaw A N k J).expect (fun z=>integral (TreeCountData.data D (map A D hk z)) N
      (coordinateCost A D hk z))=totalCoordinate (N:=N) (J:=J) A D hk := by
  change (tapeLaw A N k J).expect (fun z=>∑ t∈range N,average D.weight (coordinateCost A D hk z t))=_
  rw [Law.expect_sum]
  exact sum_congr rfl (fun t _=>expect_average _ _ _)

theorem size_finance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k) :
    (tapeLaw A N k J).expect (fun z=>sizeRefresh A D hk z N) ≤
      288*KeySizeTracker.ell (k+1)*A.q*totalCoordinate (N:=N) (J:=J) A D hk+sizeEndpoint A k J := by
  have h := (tapeLaw A N k J).expect_mono _ _ (fun z=>size_budget A D hk z N)
  simpa only [Law.expect_add,Law.expect_const,Law.expect_mul,coordinate_integral_expect] using h

theorem anchor_finance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    (tapeLaw A N k J).expect (fun z=>totalAnchorTravel A D hk z N) ≤
      anchorRate A k*(∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
        anchorEndpoint A k J := by
  have hp := (tapeLaw A N k J).expect_mono _ _ (fun z=>payment_budget A D hk z hdiam)
  simp only [Law.expect_add,Law.expect_const,Law.expect_mul,coordinate_integral_expect] at hp
  have hm : (∑ t∈range N,average D.weight (fun ω=>dist (D.position t ω (D.chosen t ω)) (D.request t ω)))=
      ∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t) := by
    apply sum_congr rfl
    intro t _
    simpa only [average,dist_comm] using (HiddenFlow.expected_mover_cost D t).symm
  rw [hm] at hp
  have hs := size_finance (N:=N) (J:=J) A D hk
  have hv := allocation_finance (N:=N) (J:=J) A D hk
  rw [add_assoc] at hv
  change _ ≤ allocationRate A k*_+allocationEndpoint A k J at hv
  have hc := coordinate_finance (N:=N) (J:=J) A D hk
  have he : 0 ≤ ((6/5:ℝ)*132)*(1+288*KeySizeTracker.ell (k+1)) := by
    have hl : 0 ≤ Real.log (k+1:ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
    unfold KeySizeTracker.ell
    positivity
  have hcm := mul_le_mul_of_nonneg_left hc he
  have ht := (tapeLaw A N k J).expect_mono _ _ (fun z=>totalAnchorTravel_le A D hk z N)
  rw [Law.expect_mul] at ht
  dsimp only [anchorRate,anchorEndpoint]
  nlinarith only [ht,hp,hs,hv,hcm]

end UniformKServer.PartitionTree

end

end OAI
