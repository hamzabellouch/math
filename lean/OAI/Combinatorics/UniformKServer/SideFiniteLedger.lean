import Mathlib
import OAI.Combinatorics.UniformKServer.CoreFiltering
import OAI.Combinatorics.UniformKServer.SideLinear
import OAI.Combinatorics.UniformKServer.SideFiniteInput

namespace OAI

                                       
section

/-! All-step side ledger with actual affine posterior coefficients fixed before
refresh. No posterior-ratio variation or after-refresh filtering is used. -/
noncomputable section
namespace UniformKServer.SideFiniteLedger
open Finset UniformKServer.AdaptiveSide UniformKServer.SideFiniteInput
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def potential (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AdaptiveSide.potential (d.param t ω) (input d t ω) (d.deficit t ω) (tracker d t ω)
def movement (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  d.deficit (t+1) ω*SideTracker.movement (tracker d (t+1) ω) (tracker d t ω)
def jump (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AdaptiveSide.potential (d.param (t+1) ω) (star d t ω) (d.deficit (t+1) ω) (prepared d t ω)-
    AdaptiveSide.potential (d.param t ω) (star d t ω) (d.deficit (t+1) ω) (prepared d t ω)
def coefficient (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι × R → ℝ :=
  CoreFiltering.liftCoefficient (fun v => SideLinear.bCoefficient (d.param t v) (tracker d t v))
    (d.flag t) ω

theorem coefficient_bound (d : Data Ω ι R) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ t ω, slope (d.param t ω) ≤ K) (t : ℕ) (ω : Ω) (ir : ι × R) :
    |coefficient d t ω ir| ≤ K := by
  apply CoreFiltering.lift_bound _ _ hK _ ω ir
  intro v i
  exact (SideLinear.bBound (d.param_valid t v) _ (tracker_state d t v) i).trans (hk t v)

theorem coefficient_measurable (d : Data Ω ι R) (t : ℕ) (ir : ι × R) :
    ConditionalLaw.measurable (d.filtration t) (fun ω => coefficient d t ω ir) := by
  apply CoreFiltering.lift_measurable
  · intro i ω v h
    dsimp only
    rw [d.param_measurable t ω v h,tracker_measurable d t h]
  · intro ω v h i r
    rw [d.flag_measurable t ω v h]

theorem frozen_change (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    AdaptiveSide.potential (d.param t ω) (oldMask d t ω) (d.deficit (t+1) ω) (tracker d t ω)-
      potential d t ω =
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1))
        (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1))
        (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω+
      SideLinear.dCoefficient (d.param t ω) (tracker d t ω)*(d.deficit (t+1) ω-d.deficit t ω) := by
  unfold potential
  rw [SideLinear.affine,SideLinear.affine]
  have hnew : oldMask d t ω = CoreFiltering.masked (d.flag t)
      (AdaptiveLedger.post d.weight (d.filtration (t+1)) (d.hidden (t+1))) ω := rfl
  have hold : input d t ω = CoreFiltering.masked (d.flag t)
      (AdaptiveLedger.post d.weight (d.filtration t) (d.hidden t)) ω := rfl
  rw [hnew,hold,CoreFiltering.masked_linear
    (fun v => SideLinear.bCoefficient (d.param t v) (tracker d t v)),
    CoreFiltering.masked_linear
    (fun v => SideLinear.bCoefficient (d.param t v) (tracker d t v))]
  have he : (∑ ir, coefficient d t ω ir*AdaptiveLedger.post d.weight (d.filtration (t+1)) (d.hidden (t+1)) ω ir)-
      (∑ ir, coefficient d t ω ir*AdaptiveLedger.post d.weight (d.filtration t) (d.hidden t) ω ir) =
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1)) (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1)) (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω := by
    simp only [AdaptiveLedger.increment,AdaptiveLedger.drift,←sum_add_distrib,←sum_sub_distrib]
    apply sum_congr rfl
    intro ir _
    ring
  change (∑ ir, coefficient d t ω ir*_)+_-((∑ ir, coefficient d t ω ir*_)+_)=_
  linarith

theorem step_bound (d : Data Ω ι R) {K : ℝ}
    (hk : ∀ t ω, slope (d.param t ω) ≤ K) (t : ℕ) (ω : Ω) :
    movement d t ω ≤ potential d t ω-potential d (t+1) ω+
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1))
        (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1))
        (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω+
      (jump d t ω+2*K*changes d t ω+K*|d.deficit (t+1) ω-d.deficit t ω|) := by
  have hs := (SideFiniteInput.step d t ω).2.2.2.2.2
  have he := errors d t ω
  have ho := input_bound (d.param_valid t ω) (star d t ω) (oldMask d t ω)
    (tracker d t ω) (d.deficit (t+1) ω) (d.deficit (t+1) ω) (tracker_state d t ω)
  have hdiff : (∑ i, |star d t ω i-oldMask d t ω i|) ≤ changes d t ω := by
    simpa only [abs_sub_comm] using he.1
  have hr : 0 ≤ changes d t ω :=
    (sum_nonneg fun i _ => abs_nonneg (oldMask d t ω i-star d t ω i)).trans he.1
  have hold : AdaptiveSide.potential (d.param t ω) (star d t ω) (d.deficit (t+1) ω) (tracker d t ω)-
      AdaptiveSide.potential (d.param t ω) (oldMask d t ω) (d.deficit (t+1) ω) (tracker d t ω) ≤ K*changes d t ω := by
    have hh := (le_abs_self _).trans ho
    simp only [sub_self,abs_zero,add_zero] at hh
    have h1 := mul_le_mul_of_nonneg_left hdiff (slope_nonneg (d.param_valid t ω))
    have h2 := mul_le_mul_of_nonneg_right (hk t ω) hr
    linarith
  have hnew : slope (d.param (t+1) ω)*(∑ i, |input d (t+1) ω i-star d t ω i|) ≤ K*changes d t ω := by
    exact (mul_le_mul_of_nonneg_left he.2.1 (slope_nonneg (d.param_valid (t+1) ω))).trans
      (mul_le_mul_of_nonneg_right (hk (t+1) ω) hr)
  have hD : SideLinear.dCoefficient (d.param t ω) (tracker d t ω)*(d.deficit (t+1) ω-d.deficit t ω) ≤
      K*|d.deficit (t+1) ω-d.deficit t ω| := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      ((SideLinear.dBound (d.param_valid t ω) _ (tracker_state d t ω)).trans (hk t ω)) (abs_nonneg _)
  have hf := frozen_change d t ω
  change movement d t ω ≤ _ at hs
  dsimp only [jump,potential,movement] at *
  linarith

theorem budget (d : Data Ω ι R) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ t ω, slope (d.param t ω) ≤ K) (H : ℕ) :
    (∑ t ∈ range H, AdaptiveLedger.expect d.weight (movement d t)) ≤
      AdaptiveLedger.expect d.weight (potential d 0)-AdaptiveLedger.expect d.weight (potential d H)+
      K*(∑ t ∈ range H, AdaptiveLedger.expect d.weight
        (fun ω => ∑ ir, |d.hidden (t+1) ω ir-d.hidden t ω ir|))+
      ∑ t ∈ range H, AdaptiveLedger.expect d.weight
        (fun ω => jump d t ω+2*K*changes d t ω+K*|d.deficit (t+1) ω-d.deficit t ω|) :=
  AdaptiveLedger.telescope d.nonneg d.filtration d.refines (coefficient d) d.hidden
    (potential d) (movement d) (fun t ω => jump d t ω+2*K*changes d t ω+K*|d.deficit (t+1) ω-d.deficit t ω|)
    hK (coefficient_bound d hK hk) (coefficient_measurable d) (step_bound d hk) H

end UniformKServer.SideFiniteLedger

end


end

end OAI
