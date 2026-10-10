import Mathlib
import OAI.Combinatorics.UniformKServer.SwitchFinite

namespace OAI

                                         
section

/-! All-step switch charge ledger with BEFORE-refresh measurable coefficients.
No stopping-event conditioning or posterior-ratio variation is used. -/
noncomputable section
namespace UniformKServer.SwitchFiniteLedger
open Finset UniformKServer.SwitchFinite
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def expense (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AlphaFiniteInput.changes d.core t ω+|d.deficit (t+1) ω-d.deficit t ω|+wholesale d t ω

theorem pointwise (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    charge d t ω/2 ≤ SwitchTracker.potential (rule d t ω) (oldMass d t ω) (d.deficit t ω)-
      potential d (t+1) ω+expense d t ω := by
  have hc : 0 ≤ AlphaFiniteInput.changes d.core t ω :=
    sum_nonneg fun i _ => SyntheticCore.changes_nonneg _ _
  have hd := abs_nonneg (d.deficit (t+1) ω-d.deficit t ω)
  by_cases hr : d.reset t ω=true
  · have hh := SwitchTracker.wholesale_step (rule d t ω) (rule d (t+1) ω)
      (oldMass_nonneg d t ω) (d.nonneg t ω)
      (Snew:=SwitchFinite.mass d (t+1) ω) (Dnew:=d.deficit (t+1) ω)
      (C:=SwitchFinite.mass d (t+1) ω+d.deficit (t+1) ω)
      (le_add_of_nonneg_right (d.nonneg (t+1) ω))
      (le_add_of_nonneg_left (mass_nonneg d (t+1) ω))
    change potential d (t+1) ω-_ ≤ _ at hh
    simp only [charge,expense,wholesale,ite_eq_left hr,zero_div]
    linarith
  · have hh := SwitchTracker.nonwholesale_step (rule d t ω)
      (oldMass d t ω) (d.deficit t ω) (SwitchFinite.mass d (t+1) ω) (d.deficit (t+1) ω)
      (AlphaFiniteInput.changes d.core t ω) (flags_error d t ω)
    have he : rule d (t+1) ω=SwitchTracker.update (rule d t ω) (SwitchFinite.mass d (t+1) ω) (d.deficit (t+1) ω) := by
      simp only [rule,ite_eq_right hr]
    rw [←he] at hh
    change potential d (t+1) ω-_ ≤ _ at hh
    simp only [charge,expense,wholesale,ite_eq_right hr,add_zero]
    linarith

theorem step_bound (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    charge d t ω/2 ≤ potential d t ω-potential d (t+1) ω+
      AdaptiveLedger.increment d.core.weight (d.core.filtration t) (d.core.filtration (t+1))
        (coefficient d t) (d.core.hidden t) ω+
      AdaptiveLedger.drift d.core.weight (d.core.filtration (t+1))
        (coefficient d t) (d.core.hidden t) (d.core.hidden (t+1)) ω+expense d t ω := by
  linarith [pointwise d t ω,frozen_change d t ω]

theorem budget (d : Data Ω ι R) (H : ℕ) :
    (∑ t ∈ range H, AdaptiveLedger.expect d.core.weight (fun ω => charge d t ω/2)) ≤
      AdaptiveLedger.expect d.core.weight (potential d 0)-AdaptiveLedger.expect d.core.weight (potential d H)+
      (∑ t ∈ range H, AdaptiveLedger.expect d.core.weight
        (fun ω => ∑ ir, |d.core.hidden (t+1) ω ir-d.core.hidden t ω ir|))+
      ∑ t ∈ range H, AdaptiveLedger.expect d.core.weight (expense d t) := by
  simpa only [one_mul] using AdaptiveLedger.telescope d.core.nonneg d.core.filtration d.core.refines
    (coefficient d) d.core.hidden (potential d) (fun t ω => charge d t ω/2) (expense d)
    (by norm_num : (0:ℝ)≤1) (coefficient_bound d) (coefficient_measurable d) (step_bound d) H

end UniformKServer.SwitchFiniteLedger

end


end

end OAI
