import Mathlib
import OAI.Combinatorics.UniformKServer.ActualPublicFlow
import OAI.Combinatorics.UniformKServer.UniformParameters

namespace OAI

noncomputable section

/-! The assembled finite-law bound: the policy is a legal causal flow, the
coefficient is absolute squared-logarithmic, and the additive quantity knows
neither the horizon nor the request law. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
def flowServe (c : Fin k→X) (r : X) (j : Fin k) : Fin k→X := Function.update c j r
local instance ixFF (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairFF : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
local instance configEqFF : DecidableEq (Fin k→X) := fun a b=>Classical.propDecidable (a=b)

theorem avg_range (w : Ω→ℝ) (f : ℕ→Ω→ℝ) (H : ℕ) :
    average w (fun ω=>∑t∈range H,f t ω)=∑t∈range H,average w (f t) :=
  CoarseData.average_range_sum w f H

theorem avg_constant (w : Ω→ℝ) (hw : ∑ω,w ω=1) (c : ℝ) :
    average w (fun _=>c)=c := CoarseData.average_const w hw c

def lawFlow (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) : RealFlow.Data X (Fin k→X) (Fin k) :=
  RealFlow.mixture (R:=X) (C:=Fin k→X) (J:=Fin k) (Z:=Tape A k N J)
    (tapeLaw A N k J) (fun z=>componentFlow (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s)

theorem lawFlow_valid (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) : RealFlow.Valid (lawFlow (N:=N) (J:=J) A D hk hdiam ω₀ hpublic s)
      flowServe PublicInput.allowed s N :=
by
  apply RealFlow.mixture_valid
  intro z
  convert component_valid (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s using 1
  funext c r j a
  simp only [flowServe,Function.update_apply]

def flowEndpoint (A : ActualPartitions.Config X) (k J : ℕ) : ℝ :=
  15840*allocationEndpoint A k J+anchorEndpoint A k J+k*(40*A.R)

theorem component_average (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) (hJ : 0<J) (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q) :
    average D.weight (fun ω=>RealFlow.flowCost (componentFlow (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s)
      (fun c r j=>dist (c j) r) [] (D.transcript N ω))≤
      15840*movement (TreeCountData.data D (map A D hk z)) (by omega) N (weight A)+
      totalAnchorTravel A D hk z N+k*(40*A.R) := by
  have hh := average_mono D.weight _ _ (fun ω=>(D.positive ω).le)
    (component_bound (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s hJ hsmall)
  simp only [average_add,avg_constant _ D.total,average_smul,avg_range] at hh
  rw [show (∑t∈range N,average D.weight (fun ω=>variation (weight A)
      (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)))=
      movement (TreeCountData.data D (map A D hk z)) (by omega) N (weight A) from
        variation_integral A D hk z N] at hh
  convert hh using 1
  · apply congrArg (average D.weight)
    funext ω
    congr 1
    apply Subsingleton.elim
  · rfl

theorem lawFlow_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) (hJ : 0<J) (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q) :
    average D.weight (fun ω=>RealFlow.flowCost (lawFlow (N:=N) (J:=J) A D hk hdiam ω₀ hpublic s)
      (fun c r j=>dist (c j) r) [] (D.transcript N ω))≤
      (15840*allocationRate A k+anchorRate A k)*
        (∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+flowEndpoint A k J := by
  have hh := (tapeLaw A N k J).expect_mono _ _ (fun z=>
    component_average (N:=N) (J:=J) A D hk z hdiam ω₀ hpublic s hJ hsmall)
  rw [expect_average] at hh
  simp only [Law.expect_add,Law.expect_mul,Law.expect_const] at hh
  have ha := allocation_finance (N:=N) (J:=J) A D hk
  rw [add_assoc] at ha
  change _≤allocationRate A k*_+allocationEndpoint A k J at ha
  have hb := anchor_finance (N:=N) (J:=J) A D hk hdiam
  simp only [lawFlow,RealFlow.mixture_cost]
  unfold flowEndpoint
  nlinarith only [hh,ha,hb]

theorem fixed_lawFlow_bound (R : ℝ) (hR : 0<R) (base : X)
    (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀ p q : X,dist p q≤40*R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) (hJ : 0<J)
    (hsmall : ∀ p q : X,p≠q → 20*radius (fixedConfig R hR base) J<dist p q) :
    average D.weight (fun ω=>RealFlow.flowCost
      (lawFlow (N:=N) (J:=J) (fixedConfig R hR base) D hk hdiam ω₀ hpublic s)
      (fun c r j=>dist (c j) r) [] (D.transcript N ω))≤
      absoluteRate*(Real.log (k+1))^2*
        (∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
      flowEndpoint (fixedConfig R hR base) k J := by
  have hh := lawFlow_bound (N:=N) (fixedConfig R hR base) D hk hdiam ω₀ hpublic s hJ hsmall
  have hm : 0≤∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t) :=
    sum_nonneg fun t _=>sum_nonneg fun ω _=>mul_nonneg (D.positive ω).le
      (sum_nonneg fun y _=>mul_nonneg ((HiddenFlow.flow D).mover_nonneg t ω y) dist_nonneg)
  have hc := mul_le_mul_of_nonneg_right (fixed_rate R hR base k (by omega)) hm
  linarith only [hh,hc]

end UniformKServer.PartitionTree

end

end OAI
