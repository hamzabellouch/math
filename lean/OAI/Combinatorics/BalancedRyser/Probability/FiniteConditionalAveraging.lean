import Mathlib.Probability.ProbabilityMassFunction.Constructions
import OAI.Combinatorics.BalancedRyser.Probability.PatternMoments

namespace OAI

namespace Balanced.FiniteConditionalAveraging

open scoped BigOperators
open PatternMoments

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

def mean (p : PMF Ω) (f : Ω → ℝ) : ℝ :=
  expectation (fun ω => (p ω).toReal) f

theorem probability_eq_mean_indicator (p : PMF Ω) (s : Set Ω) :
    (p.toOuterMeasure s).toReal = mean p (s.indicator (fun _ => 1)) := by
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : ω ∈ s <;> simp [hω]
  · intro ω _
    by_cases hω : ω ∈ s <;> simp [hω, p.apply_ne_top ω]

theorem mean_sum {A : Type*} [Fintype A] (p : PMF Ω) (f : A → Ω → ℝ) :
    mean p (fun ω => ∑ a, f a ω) = ∑ a, mean p (f a) :=
  expectation_sum _ _

theorem mean_const_mul (p : PMF Ω) (c : ℝ) (f : Ω → ℝ) :
    mean p (fun ω => c * f ω) = c * mean p f :=
  expectation_const_mul _ _ _

theorem mean_mul_const (p : PMF Ω) (f : Ω → ℝ) (c : ℝ) :
    mean p (fun ω => f ω * c) = mean p f * c :=
  expectation_mul_const _ _ _

theorem mean_nonneg (p : PMF Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean p f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg ENNReal.toReal_nonneg (hf ω))

theorem mean_filter (p : PMF Ω) (s : Set Ω)
    (hs : ∃ ω ∈ s, ω ∈ p.support) (f : Ω → ℝ) :
    mean (p.filter s hs) f = mean p (s.indicator f) / (p.toOuterMeasure s).toReal := by
  unfold mean expectation
  simp only [PMF.filter_apply, ← PMF.toOuterMeasure_apply, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ s
  · simp [Set.indicator_apply, hω, mul_assoc, mul_comm]
  · simp [Set.indicator_apply, hω]

omit [Fintype Ω] in

theorem probability_pos (p : PMF Ω) (s : Set Ω)
    (hs : ∃ ω ∈ s, ω ∈ p.support) : 0 < (p.toOuterMeasure s).toReal := by
  apply ENNReal.toReal_pos
  · intro hz
    have hd := (PMF.toOuterMeasure_apply_eq_zero_iff p s).mp hz
    obtain ⟨ω, hωs, hωp⟩ := hs
    exact Set.disjoint_left.mp hd hωp hωs
  · rw [PMF.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top s

theorem weighted_mean_le (p : PMF Ω) (hfull : ∀ ω, ω ∈ p.support)
    (expose : Ω → Y) (f Z : Ω → ℝ) (B : ℝ)
    (hf : ∀ ω, 0 ≤ f ω)
    (hdepends : ∀ ω ω', expose ω = expose ω' → f ω = f ω')
    (hbound : ∀ a, mean (p.filter {ω | expose ω = expose a}
      ⟨a, rfl, hfull a⟩) Z ≤ B) :
    mean p (fun ω => f ω * Z ω) ≤ B * mean p f := by
  classical
  apply weighted_fiber_bound (fun ω => (p ω).toReal) Z f expose B hf hdepends
  intro y
  cases isEmpty_or_nonempty {ω // expose ω = y} with
  | inl h =>
      let := h
      simp
  | inr h =>
      obtain ⟨a⟩ := h
      have ha := hbound a
      rw [mean_filter] at ha
      have hp := probability_pos p {ω | expose ω = expose a}
        ⟨a, rfl, hfull a⟩
      have hmul := (div_le_iff₀ hp).mp ha
      rw [probability_eq_mean_indicator] at hmul
      have heq : ({ω | expose ω = expose a} : Set Ω) = {ω | expose ω = y} := by
        simp only [a.property]
      rw [heq] at hmul
      have hsum (g : Ω → ℝ) : (∑ ω, if expose ω = y then g ω else 0) =
          ∑ ω : {ω // expose ω = y}, g ω := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by simp) _
      simp only [mean, expectation, Set.indicator_apply, Set.mem_ofPred_eq,
        mul_ite, mul_zero, mul_one] at hmul
      rw [hsum, hsum] at hmul
      exact hmul

end
end Balanced.FiniteConditionalAveraging

end OAI
