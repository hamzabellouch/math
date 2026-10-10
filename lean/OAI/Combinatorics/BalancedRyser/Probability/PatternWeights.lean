import OAI.Combinatorics.BalancedRyser.Probability.PatternCancellation
import OAI.Combinatorics.BalancedRyser.Probability.PatternMoments

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Balanced.PatternMoments

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]

noncomputable def weightMeasure (p : Ω → ℝ) : Measure Ω :=
  ∑ ω, ENNReal.ofReal (p ω) • Measure.dirac ω

lemma weightMeasure_univ (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) :
    weightMeasure p Set.univ = ENNReal.ofReal (∑ ω, p ω) := by
  classical
  simp [weightMeasure, Measure.finsetSum_apply, ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i)]

lemma isProbabilityMeasure_weightMeasure (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) :
    IsProbabilityMeasure (weightMeasure p) := by
  constructor
  rw [weightMeasure_univ p hp, hp1, ENNReal.ofReal_one]

lemma weightMeasure_real_singleton [MeasurableSingletonClass Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (ω : Ω) :
    (weightMeasure p).real {ω} = p ω := by
  classical
  simp [weightMeasure, Measure.real, Measure.finsetSum_apply, Pi.single_apply, hp]

lemma integral_weightMeasure_eq_expectation [MeasurableSingletonClass Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → ℝ) :
    (∫ ω, f ω ∂weightMeasure p) = expectation p f := by
  have : IsFiniteMeasure (weightMeasure p) := by
    constructor
    rw [weightMeasure_univ p hp]
    exact ENNReal.ofReal_lt_top
  rw [integral_fintype (Integrable.of_finite)]
  simp only [weightMeasure_real_singleton p hp, smul_eq_mul, expectation]

theorem expectation_centered_pattern_prod_eq_zero [MeasurableSingletonClass Ω]
    {A I : Type*} [DecidableEq A] [DecidableEq I]
    {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (ξ : (i : I) → Ω → E i)
    (hξ : iIndepFun ξ (weightMeasure p)) (hξm : ∀ i, Measurable (ξ i))
    (C : A → Finset I) (F : (a : A) → ((i : C a) → E i) → ℝ)
    (hF : ∀ a, Measurable (F a))
    (s : Finset A) {a : A} (ha : a ∈ s)
    (hdisj : ∀ b ∈ s.erase a, Disjoint (C a) (C b)) :
    expectation p (fun ω => ∏ b ∈ s,
      (F b (fun i => ξ i ω) - expectation p (fun w => F b (fun i => ξ i w)))) = 0 := by
  let : IsProbabilityMeasure (weightMeasure p) :=
    isProbabilityMeasure_weightMeasure p hp hp1
  have h := Balanced.Pattern.integral_centered_pattern_prod_eq_zero
    hξ hξm C F hF (fun _ => Integrable.of_finite) s ha hdisj
  simpa only [integral_weightMeasure_eq_expectation p hp] using h

omit [MeasurableSpace Ω]

theorem abs_expectation_le (p f : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) :
    |expectation p f| ≤ expectation p (fun ω => |f ω|) := by
  unfold expectation
  calc
    |∑ ω, p ω * f ω| ≤ ∑ ω, |p ω * f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ω, p ω * |f ω| := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [abs_mul, abs_of_nonneg (hp ω)]

theorem abs_centered_prod_le
    {A : Type*} (s : Finset A) (p : Ω → ℝ) (X : A → Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hX : ∀ a ∈ s, ∀ ω, 0 ≤ X a ω) (ω : Ω) :
    |∏ a ∈ s, (X a ω - expectation p (X a))| ≤
      ∏ a ∈ s, (X a ω + expectation p (X a)) := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod₀
  · intro a _
    exact abs_nonneg _
  · intro a ha
    have hm : 0 ≤ expectation p (X a) :=
      Finset.sum_nonneg (fun w _ => mul_nonneg (hp w) (hX a ha w))
    have hx := hX a ha ω
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_expectation_centered_prod_le
    {A : Type*} (s : Finset A) (p : Ω → ℝ) (X : A → Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hX : ∀ a ∈ s, ∀ ω, 0 ≤ X a ω) :
    |expectation p (fun ω => ∏ a ∈ s, (X a ω - expectation p (X a)))| ≤
      expectation p (fun ω => ∏ a ∈ s, (X a ω + expectation p (X a))) := by
  refine (abs_expectation_le p _ hp).trans ?_
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (abs_centered_prod_le s p X hp hX ω) (hp ω)

end Balanced.PatternMoments

end OAI
