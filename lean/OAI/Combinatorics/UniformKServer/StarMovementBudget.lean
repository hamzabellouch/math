import Mathlib
import OAI.Combinatorics.UniformKServer.StarTrackerBudgets
import OAI.Combinatorics.UniformKServer.StarAllSteps

namespace OAI

                                         
section

/-! The complete actual local movement theorem. Parent movement has coefficient
one; the absolute large coefficient multiplies only the hidden count movement.
The additive allowance is independent of both the law and the horizon. -/
noncomputable section
namespace UniformKServer.StarMovementBudget
open Finset StarRanks StarSchedules StarEnergy StarLocalCharges StarTrackerBudgets
open StarCoarseBudgets StarIntegratedJumps AllocationOutputs RankTracking CoarseData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem initial_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (fun t _ => if t=0 then 480*(k:ℝ) else 0) ≤ 480*k := by
  simp only [integral,average_const d.weight d.total]
  rw [sum_ite_eq']
  split_ifs <;> first | exact le_rfl | positivity

theorem expense_budget (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (StarAllSteps.expense d hk) ≤ (10:ℝ)^63*EpochAlpha.ell k*energy d H := by
  change integral d H (fun t ω => 4*endpoints d (StarConstants.rho/EpochAlpha.ell k) t ω+
    6*coreChanges d t ω+32*(StarOutputMovement.alphaMove d t ω+
    StarOutputMovement.sideMove d hk t ω+StarOutputMovement.deficitMove d t ω+
    StarMovementData.charge d t ω)+120*wholesaleMass d t ω+
    if t=0 then 480*(k:ℝ) else 0) ≤ _
  simp only [integral_add,integral_mul]
  have h₀ := initial_budget d H
  have he := fine_endpoints d H
  have hc := core_budget d H
  have ha := alpha_budget d H
  have hs := side_budget d hk H
  have hd := deficit_budget d H
  have hw := wholesale_budget d H
  have ht := switch_budget d H
  have hk' := (allowance_bounds ι k).2.1.trans (allowance_le_energy d H)
  have hn := mul_le_mul_of_nonneg_right (EpochAlpha.ell_one k) (energy_nonneg d H)
  nlinarith only [h₀,he,hc,ha,hs,hd,hw,ht,hk',hn,energy_nonneg d H]

theorem movement (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) (q : ℕ → Ω → ℝ)
    (hq : ∀ t ω, StarLower.parentLower d t ω ≤ q t ω) :
    integral d H (fun t ω => variation (StarAllocator.output d hk t ω (q t ω))
      (StarAllocator.output d hk (t+1) ω (q (t+1) ω))) ≤
    integral d H (fun t ω => |q (t+1) ω-q t ω|)+
      (10:ℝ)^63*EpochAlpha.ell k*cost d H+
      (10:ℝ)^63*EpochAlpha.ell k*allowance ι k := by
  have h := integral_mono d H (fun t ω => StarAllSteps.step d hk t ω (hq t ω) (hq (t+1) ω))
  simp only [integral_add] at h
  have hb := expense_budget d hk H
  unfold energy at hb
  linarith only [h,hb]

end UniformKServer.StarMovementBudget

end


end

end OAI
