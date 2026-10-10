import OAI.Combinatorics.BalancedRyser.Probability.PatternIntegrability
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentModel
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentsLemmas

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Balanced.PatternExposure

variable (P : PatternModel)

theorem measurable_fixedExpectation (K : Finset P.Color)
    (f : P.Sample → ℝ) (hf : Measurable f) :
    Measurable (fun x => P.fixedExpectation K x f) := by
  classical
  have hfix : Measurable (fun z : P.Sample × P.Sample =>
      P.fixCoordinates K z.1 z.2) := by
    unfold PatternModel.fixCoordinates
    apply Measurable.of_eval
    intro c
    by_cases hc : c ∈ K
    · simp only [ite_eq_left hc]
      fun_prop
    · simp only [ite_eq_right hc]
      fun_prop
  exact ((hf.comp hfix).stronglyMeasurable.integral_prod_right').measurable

theorem ofReal_fixedExpectation_eq_lmarginal (K : Finset P.Color)
    (x : P.Sample) (f : P.Sample → ℝ) (hf : Measurable f)
    (hn : ∀ y, 0 ≤ f y) (B : ℝ) (hB : ∀ y, ‖f y‖ ≤ B) :
    ENNReal.ofReal (P.fixedExpectation K x f) =
      lmarginal P.law (Finset.univ \ K) (fun y => ENNReal.ofReal (f y)) x := by
  rw [PatternModel.fixedExpectation, ofReal_integral_eq_lintegral_ofReal
    (P.integrable_fixed_of_bound K x hf B hB)
    (Filter.Eventually.of_forall fun y => hn _)]
  exact P.lintegral_fixCoordinates_eq_lmarginal K x _ hf.ennreal_ofReal

theorem fixedExpectation_tower_of_nonneg_bounded
    {K₀ K : Finset P.Color} (hK : K₀ ⊆ K) (x : P.Sample)
    (f : P.Sample → ℝ) (hf : Measurable f) (hn : ∀ y, 0 ≤ f y)
    (B : ℝ) (hB : ∀ y, ‖f y‖ ≤ B) :
    P.fixedExpectation K₀ x (fun y => P.fixedExpectation K y f) =
      P.fixedExpectation K₀ x f := by
  let g : P.Sample → ℝ := fun y => P.fixedExpectation K y f
  have hg : Measurable g := measurable_fixedExpectation P K f hf
  have hgn (y : P.Sample) : 0 ≤ g y := P.fixedExpectation_nonneg K y hn
  have hgB (y : P.Sample) : ‖g y‖ ≤ B := by
    change ‖∫ z, f (P.fixCoordinates K y z) ∂P.measure‖ ≤ B
    calc
      _ ≤ ∫ z, ‖f (P.fixCoordinates K y z)‖ ∂P.measure :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _z : P.Sample, B ∂P.measure :=
        integral_mono (P.integrable_fixed_of_bound K y hf B hB).norm
          (integrable_const B) (fun z => hB _)
      _ = B := by simp
  have heq : ENNReal.ofReal (P.fixedExpectation K₀ x g) =
      ENNReal.ofReal (P.fixedExpectation K₀ x f) := by
    rw [ofReal_fixedExpectation_eq_lmarginal P K₀ x g hg hgn B hgB,
      ofReal_fixedExpectation_eq_lmarginal P K₀ x f hf hn B hB]
    have hinner : (fun y => ENNReal.ofReal (g y)) =
        lmarginal P.law (Finset.univ \ K) (fun y => ENNReal.ofReal (f y)) := by
      funext y
      exact ofReal_fixedExpectation_eq_lmarginal P K y f hf hn B hB
    rw [hinner, PatternExposureKernel.exposure_tower P.law hK _ hf.ennreal_ofReal]
  have hreal := congrArg ENNReal.toReal heq
  simpa only [ENNReal.toReal_ofReal (P.fixedExpectation_nonneg K₀ x hgn),
    ENNReal.toReal_ofReal (P.fixedExpectation_nonneg K₀ x hn)] using hreal

theorem fixedExpectation_count_tower {K₀ K : Finset P.Color}
    (hK : K₀ ⊆ K) (x : P.Sample) :
    P.fixedExpectation K₀ x (fun y => P.fixedExpectation K y P.count) =
      P.fixedExpectation K₀ x P.count := by
  classical
  have hn (y : P.Sample) : 0 ≤ P.count y :=
    Finset.sum_nonneg (fun a _ => P.indicator_nonneg a y)
  apply fixedExpectation_tower_of_nonneg_bounded P hK x P.count
    P.measurable_count hn (Fintype.card P.Label : ℝ)
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg (hn y)]
  calc
    P.count y ≤ ∑ _a : P.Label, (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ => P.indicator_le_one a y)
    _ = (Fintype.card P.Label : ℝ) := by simp

theorem indicator_fixed_of_support_subset (K : Finset P.Color)
    (x y : P.Sample) (a : P.Label) (h : P.support a ⊆ K) :
    P.indicator a (P.fixCoordinates K x y) = P.indicator a x := by
  apply P.indicator_eq_of_agree
  intro c hc
  simp [PatternModel.fixCoordinates, h hc]

theorem count_fixed_of_support_subset (K : Finset P.Color)
    (x y : P.Sample) (h : ∀ a, P.support a ⊆ K) :
    P.count (P.fixCoordinates K x y) = P.count x := by
  classical
  apply Finset.sum_congr rfl
  intro a _
  exact indicator_fixed_of_support_subset P K x y a (h a)

theorem fixedExpectation_count_of_support_subset (K : Finset P.Color)
    (x : P.Sample) (h : ∀ a, P.support a ⊆ K) :
    P.fixedExpectation K x P.count = P.count x := by
  simp only [PatternModel.fixedExpectation,
    count_fixed_of_support_subset P K x _ h]
  simp

theorem centeredMoment_zero_of_support_subset (K : Finset P.Color)
    (x : P.Sample) (h : ∀ a, P.support a ⊆ K) (s : ℕ) (hs : 0 < s) :
    P.fixedExpectation K x
      (fun y => |P.count y - P.fixedExpectation K x P.count| ^ (2 * s)) = 0 := by
  rw [fixedExpectation_count_of_support_subset P K x h]
  simp only [PatternModel.fixedExpectation,
    count_fixed_of_support_subset P K x _ h, sub_self, abs_zero]
  simp [Nat.ne_of_gt hs]

end Balanced.PatternExposure

end OAI
