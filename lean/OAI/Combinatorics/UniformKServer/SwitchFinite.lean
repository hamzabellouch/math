import Mathlib
import OAI.Combinatorics.UniformKServer.CoreFiltering
import OAI.Combinatorics.UniformKServer.AlphaFiniteInput
import OAI.Combinatorics.UniformKServer.SwitchTracker

namespace OAI

                                   
section

/-! Literal causal hysteresis under finite observation laws.  The old-rule
potential is filtered on every step, before the wholesale/reset decision. -/
noncomputable section
namespace UniformKServer.SwitchFinite
open Finset UniformKServer.AlphaFiniteInput UniformKServer.SwitchTracker
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

structure Data (Ω ι R : Type*) [Fintype Ω] [Fintype ι] [Fintype R] where
  core : AlphaFiniteInput.Data Ω ι R
  deficit : ℕ → Ω → ℝ
  nonneg : ∀ t ω, 0 ≤ deficit t ω
  measurable : ∀ t ω v, (core.filtration t).r ω v → deficit t ω=deficit t v
  reset : ℕ → Ω → Bool
  reset_measurable : ∀ t ω v, (core.filtration (t+1)).r ω v → reset t ω=reset t v

def mass (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ := ∑ i, input d.core t ω i

def oldMass (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ := ∑ i, oldMask d.core t ω i

def rule (d : Data Ω ι R) : ℕ → Ω → Rule
  | 0, ω => update .one (mass d 0 ω) (d.deficit 0 ω)
  | t+1, ω => update (if d.reset t ω then .one else rule d t ω)
      (mass d (t+1) ω) (d.deficit (t+1) ω)

def potential (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  SwitchTracker.potential (rule d t ω) (mass d t ω) (d.deficit t ω)

def charge (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  if d.reset t ω then 0 else SwitchTracker.charge (rule d t ω) (mass d (t+1) ω) (d.deficit (t+1) ω)

def wholesale (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  if d.reset t ω then mass d (t+1) ω+d.deficit (t+1) ω else 0

def indicator (rule : Rule) : ℝ := if rule=.two then 1 else 0

def coefficient (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι × R → ℝ :=
  CoreFiltering.liftCoefficient (fun v _ => indicator (rule d t v)) (d.core.flag t) ω

theorem mass_nonneg (d : Data Ω ι R) (t : ℕ) (ω : Ω) : 0 ≤ mass d t ω :=
  sum_nonneg fun i _ => input_nonneg d.core t ω i

theorem oldMass_nonneg (d : Data Ω ι R) (t : ℕ) (ω : Ω) : 0 ≤ oldMass d t ω :=
  sum_nonneg fun i _ => SyntheticCore.input_nonneg (fun r => (post_range d.core (t+1) ω i r).1) _

theorem rule_valid (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    valid (rule d t ω) (mass d t ω) (d.deficit t ω) := by
  cases t <;> exact update_valid _ (mass_nonneg d _ ω) (d.nonneg _ ω)

theorem mass_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.core.filtration t).r ω v) : mass d t ω=mass d t v := by
  unfold mass
  rw [input_measurable d.core t h]

theorem rule_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.core.filtration t).r ω v) : rule d t ω=rule d t v := by
  induction t with
  | zero => rw [rule,rule,mass_measurable d 0 h,d.measurable 0 ω v h]
  | succ t ih =>
    rw [rule,rule,d.reset_measurable t ω v h,ih (d.core.refines t ω v h),
      mass_measurable d (t+1) h,d.measurable (t+1) ω v h]

theorem coefficient_bound (d : Data Ω ι R) (t : ℕ) (ω : Ω) (ir : ι × R) :
    |coefficient d t ω ir| ≤ 1 := by
  apply CoreFiltering.lift_bound _ _ (by norm_num) _ ω ir
  intro v i
  unfold indicator
  split_ifs <;> norm_num

theorem coefficient_measurable (d : Data Ω ι R) (t : ℕ) (ir : ι × R) :
    ConditionalLaw.measurable (d.core.filtration t) (fun ω => coefficient d t ω ir) := by
  apply CoreFiltering.lift_measurable
  · intro i ω v h
    dsimp only
    rw [rule_measurable d t h]
  · intro ω v h i r
    rw [d.core.flag_measurable t ω v h]

theorem flags_error (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    |mass d (t+1) ω-oldMass d t ω| ≤ changes d.core t ω := by
  unfold mass oldMass
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_sub_comm]
  exact SyntheticCore.input_difference _ _ _ (post_range d.core (t+1) ω i)

theorem affine (r : Rule) (S D : ℝ) :
    SwitchTracker.potential r S D=indicator r*S+(1-indicator r)*D := by
  have hn : Rule.one ≠ Rule.two := by intro h; cases h
  cases r <;> simp [SwitchTracker.potential,indicator,hn]

theorem frozen_change (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    SwitchTracker.potential (rule d t ω) (oldMass d t ω) (d.deficit t ω)-potential d t ω =
      AdaptiveLedger.increment d.core.weight (d.core.filtration t) (d.core.filtration (t+1))
        (coefficient d t) (d.core.hidden t) ω+
      AdaptiveLedger.drift d.core.weight (d.core.filtration (t+1))
        (coefficient d t) (d.core.hidden t) (d.core.hidden (t+1)) ω := by
  unfold potential
  rw [affine,affine]
  have hx : ∀ (s : ℕ) (f : ℕ), indicator (rule d t ω)*(∑ i, SyntheticCore.input
      (post d.core s ω i) (d.core.flag f ω i)) =
      ∑ ir, CoreFiltering.liftCoefficient (fun v _ => indicator (rule d t v))
        (d.core.flag f) ω ir*AdaptiveLedger.post d.core.weight (d.core.filtration s) (d.core.hidden s) ω ir := by
    intro s f
    rw [mul_sum]
    exact CoreFiltering.masked_linear (fun v (_ : ι) => indicator (rule d t v)) (d.core.flag f)
      (AdaptiveLedger.post d.core.weight (d.core.filtration s) (d.core.hidden s)) ω
  unfold mass oldMass input oldMask
  rw [hx,hx]
  rw [show ∀ a b c : ℝ, a+c-(b+c)=a-b by intros; ring]
  simp only [AdaptiveLedger.increment,AdaptiveLedger.drift,←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro ir _
  unfold coefficient
  ring

end UniformKServer.SwitchFinite

end


end

end OAI
