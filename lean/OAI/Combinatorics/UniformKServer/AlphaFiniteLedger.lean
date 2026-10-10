import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaEmptyLinear
import OAI.Combinatorics.UniformKServer.AlphaFiniteInput

namespace OAI

                                        
section

/-! The actual alpha trajectory has an all-step finite-law movement ledger.
 Filtering coefficients are the primitives' proved affine coefficients and are
 measured before refresh tests. Parameter jumps remain their exact signed
 values for the subsequent sparse-charge estimate. -/
noncomputable section
namespace UniformKServer.AlphaFiniteLedger
open Finset UniformKServer.AlphaEmpty UniformKServer.AlphaFiniteInput
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def potential (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AlphaEmpty.potential (d.param t ω) (input d t ω) (alpha d t ω)

def movement (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  (∑ i, input d (t+1) ω i)*SimplexTracker.movement (alpha d (t+1) ω) (alpha d t ω)

def jump (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AlphaEmpty.potential (d.param (t+1) ω) (star d t ω) (prepared d t ω)-
    AlphaEmpty.potential (d.param t ω) (star d t ω) (prepared d t ω)

def coefficient (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι × R → ℝ :=
  CoreFiltering.liftCoefficient (fun v => AlphaEmptyLinear.coefficient (d.param t v) (alpha d t v))
    (d.flag t) ω

theorem coefficient_bound (d : Data Ω ι R) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ t ω, scale (d.param t ω) ≤ K) (t : ℕ) (ω : Ω) (ir : ι × R) :
    |coefficient d t ω ir| ≤ 15*K := by
  apply CoreFiltering.lift_bound _ _ (by positivity) _ ω ir
  intro v i
  exact (AlphaEmptyLinear.bound (d.param_valid t v) _ (alpha_state d t v) i).trans
    (mul_le_mul_of_nonneg_left (hk t v) (by norm_num))

theorem coefficient_measurable (d : Data Ω ι R) (t : ℕ) (ir : ι × R) :
    ConditionalLaw.measurable (d.filtration t) (fun ω => coefficient d t ω ir) := by
  apply CoreFiltering.lift_measurable
  · intro i ω v h
    dsimp only
    rw [d.param_measurable t ω v h,alpha_measurable d t h]
  · intro ω v h i r
    rw [d.flag_measurable t ω v h]

theorem frozen_change (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    AlphaEmpty.potential (d.param t ω) (oldMask d t ω) (alpha d t ω)-potential d t ω =
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1))
        (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1))
        (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω := by
  have ha := AlphaEmpty.state_interval (alpha_state d t ω)
  unfold potential
  rw [AlphaEmptyLinear.affine (d.param_valid t ω) _ _ ha,
    AlphaEmptyLinear.affine (d.param_valid t ω) _ _ ha]
  have hnew : oldMask d t ω = CoreFiltering.masked (d.flag t)
      (AdaptiveLedger.post d.weight (d.filtration (t+1)) (d.hidden (t+1))) ω := rfl
  have hold : input d t ω = CoreFiltering.masked (d.flag t)
      (AdaptiveLedger.post d.weight (d.filtration t) (d.hidden t)) ω := rfl
  rw [hnew,hold,CoreFiltering.masked_linear
    (fun v => AlphaEmptyLinear.coefficient (d.param t v) (alpha d t v)),
    CoreFiltering.masked_linear
    (fun v => AlphaEmptyLinear.coefficient (d.param t v) (alpha d t v))]
  simp only [AdaptiveLedger.increment,AdaptiveLedger.drift,←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro ir _
  change coefficient d t ω ir * _-coefficient d t ω ir * _ = _
  ring

theorem step_bound (d : Data Ω ι R) {K : ℝ}
    (hk : ∀ t ω, scale (d.param t ω) ≤ K) (t : ℕ) (ω : Ω) :
    movement d t ω ≤ potential d t ω-potential d (t+1) ω+
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1))
        (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1))
        (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω+
      (jump d t ω+(30*K+4)*changes d t ω) := by
  have hs := (AlphaFiniteInput.step d t ω).2.2.2.2
  have he := errors d t ω
  have ho := AlphaEmpty.input_bound (d.param_valid t ω) (star d t ω) (oldMask d t ω)
    (alpha d t ω) (alpha_state d t ω)
  have hdiff : (∑ i, |star d t ω i-oldMask d t ω i|) ≤ changes d t ω := by
    simpa only [abs_sub_comm] using he.1
  have hr : 0 ≤ changes d t ω := sum_nonneg fun i _ => SyntheticCore.changes_nonneg _ _
  have hold : AlphaEmpty.potential (d.param t ω) (star d t ω) (alpha d t ω) ≤
      AlphaEmpty.potential (d.param t ω) (oldMask d t ω) (alpha d t ω)+15*K*changes d t ω := by
    have hb := (le_abs_self _).trans (ho.trans (mul_le_mul_of_nonneg_left hdiff
      (mul_nonneg (by norm_num) (scale_nonneg (d.param_valid t ω)))))
    have hb' := mul_le_mul_of_nonneg_right (hk t ω) hr
    nlinarith
  have hnew : 15*scale (d.param (t+1) ω)*(∑ i, |input d (t+1) ω i-star d t ω i|) ≤
      15*K*changes d t ω := by
    apply (mul_le_mul_of_nonneg_left he.2.1
      (mul_nonneg (by norm_num) (scale_nonneg (d.param_valid (t+1) ω)))).trans
    have hb := mul_le_mul_of_nonneg_right (hk (t+1) ω) hr
    nlinarith
  have hf := frozen_change d t ω
  change movement d t ω ≤ _ at hs
  change _ - potential d t ω = _ at hf
  dsimp only [jump,potential,movement] at *
  nlinarith [he.2.2.2]

theorem budget (d : Data Ω ι R) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ t ω, scale (d.param t ω) ≤ K) (H : ℕ) :
    (∑ t ∈ range H, AdaptiveLedger.expect d.weight (movement d t)) ≤
      AdaptiveLedger.expect d.weight (potential d 0)-AdaptiveLedger.expect d.weight (potential d H)+
      15*K*(∑ t ∈ range H, AdaptiveLedger.expect d.weight
        (fun ω => ∑ ir, |d.hidden (t+1) ω ir-d.hidden t ω ir|))+
      ∑ t ∈ range H, AdaptiveLedger.expect d.weight
        (fun ω => jump d t ω+(30*K+4)*changes d t ω) :=
  AdaptiveLedger.telescope d.nonneg d.filtration d.refines (coefficient d) d.hidden
    (potential d) (movement d) (fun t ω => jump d t ω+(30*K+4)*changes d t ω)
    (by positivity) (coefficient_bound d hK hk) (coefficient_measurable d)
    (step_bound d hk) H

end UniformKServer.AlphaFiniteLedger

end


end

end OAI
