import OAI.Probability.InvariantIsing.Cavity.CavityCylinderPenalty
import OAI.Probability.InvariantIsing.Cavity.CavityBaseExhaustion

namespace OAI

/-! The nonuniform covariance comparison on the actual countable prior.
Finite restrictions converge in expected log partition, retaining the
cavity-size penalty without replacing it by a uniform maximum. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem countable_cylinder_covariance_penalty_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H V : X → ℝ) (c : ℝ)
    {M D : ℝ} (hH : ∀ x, |H x| ≤ M) (hV : ∀ x, |V x| ≤ D)
    (C A : X → ℕ →₀ ℝ) {B₀ B₁ : ℝ}
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x - 2 * c * V x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  obtain ⟨S, hS, hpos, hExh⟩ := countable_reference_exhaustion ν
  have hp : ∀ x, |H x - 2 * c * V x| ≤ M + 2 * |c| * D := by
    intro x
    calc
      _ ≤ |H x| + |2 * c * V x| := abs_sub _ _
      _ = |H x| + 2 * |c| * |V x| := by norm_num [abs_mul]
      _ ≤ _ := add_le_add (hH x) (mul_le_mul_of_nonneg_left (hV x) (by positivity))
  have hm₀ := cavity_bounded_base_restriction_mean_tendsto ν
    (fun x => H x - 2 * c * V x) hp C hC (fun n => (hS n).measurableSet) hExh hpos
  have hm₁ := cavity_bounded_base_restriction_mean_tendsto ν H hH A hA
    (fun n => (hS n).measurableSet) hExh hpos
  apply le_of_tendsto_of_tendsto hm₀ hm₁
  apply Eventually.of_forall
  intro n
  let := (hS n).fintype
  have : IsProbabilityMeasure (subtypeReference ν (S n)) :=
    subtypeReference_probability ν (hS n).measurableSet (hpos n)
  have hf := finite_cylinder_covariance_penalty_comparison (subtypeReference ν (S n))
    (fun x => H x) (fun x => V x) c (fun x => C x) (fun x => A x)
    (fun x y => hK x y)
  have he (J : X → ℝ) (Q : X → ℕ →₀ ℝ) (g : ℕ → ℝ) :
      (∫ x : S n, Real.exp (J x + cylinderField (Q x) g) ∂subtypeReference ν (S n)) =
      ∫ x, Real.exp (J x + cylinderField (Q x) g) ∂normalizedRestriction ν (S n) :=
    (subtypeReference_preserving ν (hS n).measurableSet).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (J x + cylinderField (Q x) g))).aestronglyMeasurable
  simpa only [he (fun x => H x - 2 * c * V x) C, he H A] using hf

end InvariantIsing

end

end OAI
