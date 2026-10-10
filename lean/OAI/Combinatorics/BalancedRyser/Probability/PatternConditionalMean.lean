import OAI.Combinatorics.BalancedRyser.Probability.PatternFixedEventAveraging
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentTails

namespace OAI

open MeasureTheory

namespace Balanced.PatternModel

universe u

theorem measurable_fixCoordinates_joint (P : PatternModel.{u}) (K : Finset P.Color) :
    Measurable (fun z : P.Sample × P.Sample => P.fixCoordinates K z.1 z.2) := by
  classical
  apply Measurable.of_eval
  intro c
  by_cases hc : c ∈ K
  · simpa [fixCoordinates, hc, Function.comp_def] using
      ((measurable_pi_apply c).comp measurable_fst :
        Measurable (fun z : P.Sample × P.Sample => z.1 c))
  · simpa [fixCoordinates, hc, Function.comp_def] using
      ((measurable_pi_apply c).comp measurable_snd :
        Measurable (fun z : P.Sample × P.Sample => z.2 c))

theorem measurable_fixedExpectation (P : PatternModel.{u}) (K : Finset P.Color)
    {f : P.Sample → ℝ} (hf : Measurable f) :
    Measurable (fun x => P.fixedExpectation K x f) := by
  have h := (hf.comp (P.measurable_fixCoordinates_joint K)).stronglyMeasurable
  exact h.integral_prod_right'.measurable

theorem fixedExpectation_eq_of_agree (P : PatternModel.{u}) (K : Finset P.Color)
    (x y : P.Sample) (hxy : ∀ c ∈ K, x c = y c) (f : P.Sample → ℝ) :
    P.fixedExpectation K x f = P.fixedExpectation K y f := by
  have heq (ω : P.Sample) : P.fixCoordinates K x ω = P.fixCoordinates K y ω := by
    funext c
    by_cases hc : c ∈ K
    · simpa [fixCoordinates, hc] using hxy c hc
    · simp [fixCoordinates, hc]
  simp only [fixedExpectation, heq]

theorem fixedExpectation_fixCoordinates (P : PatternModel.{u}) (K : Finset P.Color)
    (x ω : P.Sample) (f : P.Sample → ℝ) :
    P.fixedExpectation K (P.fixCoordinates K x ω) f = P.fixedExpectation K x f := by
  apply P.fixedExpectation_eq_of_agree K
  intro c hc
  simp [fixCoordinates, hc]

end Balanced.PatternModel

namespace Balanced.PatternTails

universe u

theorem allowed_count_tail_le (P : PatternModel.{u}) (K : Finset P.Color)
    (S : Set P.Sample) (hS : MeasurableSet S)
    (hdepends : ∀ x y, (∀ c ∈ K, x c = y c) → (x ∈ S ↔ y ∈ S))
    (t : ℝ) (ht : 0 < t) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hmom : ∀ x ∈ S, P.fixedExpectation K x (fun ω => P.count ω ^ n) ≤ C) :
    P.measure.real (S ∩ {ω | t ≤ P.count ω}) ≤
      (C / t ^ n) * P.measure.real S := by
  apply P.measureReal_inter_le_of_fixed_measureReal_le K S _ hS
    (measurableSet_le measurable_const P.measurable_count) hdepends
    _ (div_nonneg hC (pow_nonneg ht.le _))
  intro x hx
  exact (count_tail_le P K x t ht n).trans
    (div_le_div_of_nonneg_right (hmom x hx) (pow_nonneg ht.le _))

theorem allowed_centered_count_tail_le (P : PatternModel.{u}) (K : Finset P.Color)
    (S : Set P.Sample) (hS : MeasurableSet S)
    (hdepends : ∀ x y, (∀ c ∈ K, x c = y c) → (x ∈ S ↔ y ∈ S))
    (t : ℝ) (ht : 0 < t) (s : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hmom : ∀ x ∈ S, P.fixedExpectation K x
      (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) ≤ C) :
    P.measure.real (S ∩ {ω | t ≤ |P.count ω - P.fixedExpectation K ω P.count|}) ≤
      (C / t ^ (2 * s)) * P.measure.real S := by
  have hm := P.measurable_fixedExpectation K P.measurable_count
  apply P.measureReal_inter_le_of_fixed_measureReal_le K S _ hS
    (measurableSet_le measurable_const ((P.measurable_count.sub hm).abs)) hdepends
    _ (div_nonneg hC (pow_nonneg ht.le _))
  intro x hx
  have h := (centered_tail_le P K x t ht s).trans
    (div_le_div_of_nonneg_right (hmom x hx) (pow_nonneg ht.le _))
  simpa only [Set.preimage_ofPred_eq, Pi.sub_apply,
    P.fixedExpectation_fixCoordinates] using h

end Balanced.PatternTails

end OAI
