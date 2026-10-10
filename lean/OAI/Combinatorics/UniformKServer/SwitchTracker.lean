import Mathlib

namespace OAI

                                    
section

/-! Literal hysteresis of the two allocation-rule outputs and its drop
 potential. This is not total-variation tracking of S: only changes of the
 old-rule potential after filtering enter the all-step ledger. -/
namespace UniformKServer.SwitchTracker

inductive Rule where
  | one | two
  deriving DecidableEq

noncomputable def update (old : Rule) (S D : ℝ) : Rule :=
  match old with
  | .one => if S < D/2 then .two else .one
  | .two => if 2*D < S then .one else .two

def valid (rule : Rule) (S D : ℝ) : Prop :=
  match rule with
  | .one => D/2 ≤ S
  | .two => S ≤ 2*D

def potential (rule : Rule) (S D : ℝ) : ℝ :=
  match rule with
  | .one => D
  | .two => S

noncomputable def charge (old : Rule) (S D : ℝ) : ℝ :=
  match old with
  | .one => if S < D/2 then D else 0
  | .two => if 2*D < S then S else 0

theorem update_valid (old : Rule) {S D : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D) :
    valid (update old S D) S D := by
  cases old <;> unfold update <;> split_ifs <;> simp only [valid] <;> linarith

theorem potential_nonneg (rule : Rule) {S D : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D) :
    0 ≤ potential rule S D := by cases rule <;> assumption

theorem charge_nonneg (rule : Rule) {S D : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D) :
    0 ≤ charge rule S D := by cases rule <;> unfold charge <;> split_ifs <;> linarith

/-- The actual Rule I→II charge is D, and II→I charge is S. -/
theorem switch_drop (old : Rule) (S D : ℝ) :
    potential (update old S D) S D ≤ potential old S D-charge old S D/2 := by
  cases old <;> unfold update charge <;> split_ifs <;> simp only [potential] <;> linarith

theorem input_slope (old : Rule) (S D S' D' : ℝ) :
    potential old S' D'-potential old S D ≤ |S'-S|+|D'-D| := by
  cases old <;> simp only [potential]
  · linarith [le_abs_self (D'-D),abs_nonneg (S'-S)]
  · linarith [le_abs_self (S'-S),abs_nonneg (D'-D)]

/-- New S here is compared to the OLD flag sum at NEW posteriors.  Thus its
 error is the number of flag changes, not absolute posterior variation. -/
theorem nonwholesale_step (old : Rule) (Sbar Dold Snew Dnew K : ℝ)
    (hK : |Snew-Sbar| ≤ K) :
    potential (update old Snew Dnew) Snew Dnew-potential old Sbar Dold ≤
      K+|Dnew-Dold|-charge old Snew Dnew/2 := by
  have h₁ := switch_drop old Snew Dnew
  have h₂ := input_slope old Sbar Dold Snew Dnew
  linarith

/-- At wholesale resets no switch credit is claimed. -/
theorem wholesale_step (old new : Rule) {Sbar Dold Snew Dnew C : ℝ}
    (hS : 0 ≤ Sbar) (hD : 0 ≤ Dold) (hSC : Snew ≤ C) (hDC : Dnew ≤ C) :
    potential new Snew Dnew-potential old Sbar Dold ≤ C := by
  have hp := potential_nonneg old hS hD
  cases old <;> cases new <;> simp only [potential] at * <;> linarith

end UniformKServer.SwitchTracker

end

end OAI
