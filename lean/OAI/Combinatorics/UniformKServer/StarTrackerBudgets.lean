import Mathlib
import OAI.Combinatorics.UniformKServer.StarIntegratedJumps
import OAI.Combinatorics.UniformKServer.SwitchFiniteLedger
import OAI.Combinatorics.UniformKServer.StarPotentialBounds

namespace OAI

                                         
section

/-! Actual minimizer and hysteresis budgets, composed from their all-step
filtering identities. The logarithmic slope is used only on coarse data. -/
noncomputable section
namespace UniformKServer.StarTrackerBudgets
open Finset StarRanks StarSchedules RankTracking CoarseData StarLocalCharges StarEnergy
open StarActualJumps StarCoarseBudgets StarIntegratedJumps StarPotentialBounds StarOutputData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem alpha_ledger (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarOutputMovement.alphaMove d) ≤ 2400*alphaScale k*k+
      15*alphaScale k*cost d H+integral d H (AlphaFiniteLedger.jump (alphaData d))+
      (30*alphaScale k+4)*integral d H (coreChanges d) := by
  have h := AlphaFiniteLedger.budget (alphaData d) (scale_nonneg k) (alpha_scale d) H
  simp only [hidden_move] at h
  change integral d H (StarOutputMovement.alphaMove d) ≤
    average d.weight (AlphaFiniteLedger.potential (alphaData d) 0)-
    average d.weight (AlphaFiniteLedger.potential (alphaData d) H)+15*alphaScale k*cost d H+
    integral d H (fun t ω => AlphaFiniteLedger.jump (alphaData d) t ω+
      (30*alphaScale k+4)*AlphaFiniteInput.changes (alphaData d) t ω) at h
  simp only [alpha_changes,integral_add,integral_mul] at h
  have h₀ := (average_interval d (alpha_potential d 0)).2
  have hH := (average_interval d (alpha_potential d H)).1
  linarith only [h,h₀,hH]

theorem side_ledger (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (StarOutputMovement.sideMove d hk) ≤ 640*sideSlope k*k+
      sideSlope k*cost d H+integral d H (SideFiniteLedger.jump (sideData d hk))+
      2*sideSlope k*integral d H (SideFiniteInput.changes (sideData d hk))+
      sideSlope k*integral d H (StarOutputMovement.deficitMove d) := by
  have h := SideFiniteLedger.budget (sideData d hk) (slope_nonneg k) (fun _ _ => le_rfl) H
  have hh (t : ℕ) (ω : Ω) : (∑ ir, |(sideData d hk).hidden (t+1) ω ir-(sideData d hk).hidden t ω ir|)=countMove d t ω :=
    hidden_move d t ω
  simp only [hh] at h
  change integral d H (StarOutputMovement.sideMove d hk) ≤
    average d.weight (SideFiniteLedger.potential (sideData d hk) 0)-
    average d.weight (SideFiniteLedger.potential (sideData d hk) H)+sideSlope k*cost d H+
    integral d H (fun t ω => SideFiniteLedger.jump (sideData d hk) t ω+
      2*sideSlope k*SideFiniteInput.changes (sideData d hk) t ω+
      sideSlope k*StarOutputMovement.deficitMove d t ω) at h
  simp only [integral_add,integral_mul] at h
  have h₀ := (average_interval d (side_potential d hk 0)).2
  have hH := (average_interval d (side_potential d hk H)).1
  linarith only [h,h₀,hH]

theorem switch_ledger (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarMovementData.charge d) ≤ 480*k+2*cost d H+
      2*integral d H (coreChanges d)+2*integral d H (StarOutputMovement.deficitMove d)+
      320*integral d H (wholesaleMass d) := by
  have h := SwitchFiniteLedger.budget (StarAllocator.switchData d) H
  have hh (t : ℕ) (ω : Ω) : (∑ ir, |(StarAllocator.switchData d).core.hidden (t+1) ω ir-
      (StarAllocator.switchData d).core.hidden t ω ir|)=countMove d t ω := hidden_move d t ω
  simp only [hh] at h
  change integral d H (fun t ω => StarMovementData.charge d t ω/2) ≤
    average d.weight (SwitchFinite.potential (StarAllocator.switchData d) 0)-
    average d.weight (SwitchFinite.potential (StarAllocator.switchData d) H)+cost d H+
    integral d H (SwitchFiniteLedger.expense (StarAllocator.switchData d)) at h
  have he := integral_mono d H (fun t ω => show SwitchFiniteLedger.expense (StarAllocator.switchData d) t ω ≤
      coreChanges d t ω+StarOutputMovement.deficitMove d t ω+160*wholesaleMass d t ω from by
    unfold SwitchFiniteLedger.expense
    change AlphaFiniteInput.changes (alphaData d) t ω + StarOutputMovement.deficitMove d t ω +
      SwitchFinite.wholesale (StarAllocator.switchData d) t ω ≤ _
    rw [alpha_changes]
    exact add_le_add le_rfl (switch_wholesale d t ω))
  simp only [integral_add,integral_mul] at he
  have h₀ : average d.weight (SwitchFinite.potential (StarAllocator.switchData d) 0) ≤ 240*k := by
    rw [←average_const d.weight d.total (240*k)]
    exact average_mono (fun ω => (d.positive ω).le) (fun ω => (switch_potential d 0 ω).2)
  have hH : 0 ≤ average d.weight (SwitchFinite.potential (StarAllocator.switchData d) H) :=
    sum_nonneg fun ω _ => mul_nonneg (d.positive ω).le (switch_potential d H ω).1
  have hm : integral d H (fun t ω => StarMovementData.charge d t ω/2)=
      (1/2)*integral d H (StarMovementData.charge d) := by
    simp only [div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹,integral_mul]
    ring
  rw [hm] at h
  linarith only [h,he,h₀,hH]

theorem alpha_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarOutputMovement.alphaMove d) ≤ (10:ℝ)^58*EpochAlpha.ell k*energy d H := by
  have h := alpha_ledger d H
  have he := EpochAlpha.ell_one k
  have hc := mul_le_mul_of_nonneg_left (cost_le_energy d H) (scale_nonneg k)
  have hk := mul_le_mul_of_nonneg_left ((allowance_bounds ι k).2.1.trans (allowance_le_energy d H)) (scale_nonneg k)
  have hf := mul_le_mul_of_nonneg_left (core_budget d H) (show 0 ≤ 30*alphaScale k+4 by positivity [scale_nonneg k])
  have hj := alpha_jump_budget d H
  have hn := mul_le_mul_of_nonneg_right he (energy_nonneg d H)
  norm_num [alphaScale,StarConstants.multiplier] at h hc hk hf
  nlinarith only [h,hc,hk,hf,hj,hn,energy_nonneg d H]

theorem side_budget (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (StarOutputMovement.sideMove d hk) ≤ (10:ℝ)^58*EpochAlpha.ell k*energy d H := by
  have h := side_ledger d hk H
  have hc := mul_le_mul_of_nonneg_left (cost_le_energy d H) (slope_nonneg k)
  have hk' := mul_le_mul_of_nonneg_left ((allowance_bounds ι k).2.1.trans (allowance_le_energy d H)) (slope_nonneg k)
  have hf := mul_le_mul_of_nonneg_left (side_flags_budget d hk H) (slope_nonneg k)
  have hd := mul_le_mul_of_nonneg_left (deficit_budget d H) (slope_nonneg k)
  have hj := side_jump_budget d hk H
  have hb := mul_le_mul_of_nonneg_right (slope_bound k) (energy_nonneg d H)
  have hn := mul_le_mul_of_nonneg_right (EpochAlpha.ell_one k) (energy_nonneg d H)
  nlinarith only [h,hc,hk',hf,hd,hj,hb,hn,energy_nonneg d H]

theorem switch_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarMovementData.charge d) ≤ (10:ℝ)^38*energy d H := by
  have h := switch_ledger d H
  have hk := (allowance_bounds ι k).2.1.trans (allowance_le_energy d H)
  nlinarith only [h,hk,cost_le_energy d H,core_budget d H,deficit_budget d H,
    wholesale_budget d H,energy_nonneg d H]

end UniformKServer.StarTrackerBudgets

end


end

end OAI
