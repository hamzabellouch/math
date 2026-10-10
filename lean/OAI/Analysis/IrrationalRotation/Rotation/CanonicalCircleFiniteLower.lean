import OAI.Analysis.IrrationalRotation.Rotation.CanonicalCircleCoefficients
import OAI.Analysis.IrrationalRotation.Rotation.ProjectionCocycleWindow
import OAI.Analysis.IrrationalRotation.Analysis.FiniteWindowIntegralLower

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem parameter_convolution_sum_lower (j : ℕ) (hj : 1 ≤ j)
    (A B : ℤ → ℂ)
    (hA : ∀ v : ℤ, |v| ≤ (p.K j : ℤ) → ‖A v‖ ≤ p.coefficientBound j)
    (hB : ∀ v : ℤ, |v| ≤ (p.K j : ℤ) → ‖B v‖ ≤ p.coefficientBound j)
    (hA0 : 1 / (j : ℝ) ≤ ‖A 0‖) (hB0 : 1 / (j : ℝ) ≤ ‖B 0‖) :
    p.ε j ≤ ∑ n ∈ Finset.range (2 * p.K j + 1),
      ‖FiniteWindow.convolution (p.K j) A B n‖ := by
  apply FiniteWindow.convolution_sum_lower_bound_of_supported_bound
    (p.K j) (p.coefficientBound j) (1 / (j : ℝ)) (p.ε j) ?_
    A B hA hB hA0 hB0
  simpa only [CircleParameterData.convolutionCoefficient] using hp.polynomial_lower j hj

theorem canonical_projection_coefficient_properties (j : ℕ) (hj : 1 ≤ j)
    (x y : Circle)
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < p.coordinate i y)
    (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (a : ℝ) (hPdiag : a ≤ ((P ProjectionCocycleWindow.basisZero) 0).re)
    (hQdiag : ((Q ProjectionCocycleWindow.basisZero) 0).re ≤ 1 - a) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(P ProjectionCocycleWindow.basisZero) v / (p.floorCocycle θ v x : ℂ)‖ ≤
        p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(p.floorCocycle θ (-v) y : ℂ) *
        conj (((1 - Q) ProjectionCocycleWindow.basisZero) (-v))‖ ≤
        p.coefficientBound j) ∧
    a ≤ ‖(P ProjectionCocycleWindow.basisZero) 0 / (p.floorCocycle θ 0 x : ℂ)‖ ∧
    a ≤ ‖(p.floorCocycle θ 0 y : ℂ) *
      conj (((1 - Q) ProjectionCocycleWindow.basisZero) 0)‖ := by
  simpa only [hp.parameter_cocycle_eq_product] using
    ProjectionCocycleWindow.circle_coefficient_properties hp j hj x y hleft hright
      P Q hP hQ a hPdiag hQdiag

theorem canonical_projection_convolution_lower (j : ℕ) (hj : 1 ≤ j)
    (x y : Circle)
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < p.coordinate i y)
    (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPdiag : 1 / (j : ℝ) ≤ ((P ProjectionCocycleWindow.basisZero) 0).re)
    (hQdiag : ((Q ProjectionCocycleWindow.basisZero) 0).re ≤ 1 - 1 / (j : ℝ)) :
    p.ε j ≤ ∑ n ∈ Finset.range (2 * p.K j + 1),
      ‖FiniteWindow.convolution (p.K j)
        (fun v => (P ProjectionCocycleWindow.basisZero) v / (p.floorCocycle θ v x : ℂ))
        (fun v => (p.floorCocycle θ (-v) y : ℂ) *
          conj (((1 - Q) ProjectionCocycleWindow.basisZero) (-v))) n‖ := by
  obtain ⟨hA, hB, hA0, hB0⟩ := hp.canonical_projection_coefficient_properties
    j hj x y hleft hright P Q hP hQ (1 / (j : ℝ)) hPdiag hQdiag
  exact hp.parameter_convolution_sum_lower j hj _ _ hA hB hA0 hB0

theorem canonical_raw_projection_convolution_lower (j : ℕ) (hj : 1 ≤ j)
    (d e : MixedRadix.Digits (MixedRadix.radices p.q))
    (hd : MixedRadix.Nonterminal d) (he : MixedRadix.Nonterminal e)
    (X Y : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (hdigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * X i⌋₊ = (d i : ℕ))
    (hedigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * Y i⌋₊ = (e i : ℕ))
    (hcurrent : ∀ i ∈ p.block j,
      X i < 1 - 3 / (p.m j : ℝ) ∧ 3 / (p.m j : ℝ) < Y i)
    (hfuture : ∀ s, j < s → ∀ i ∈ p.block s,
      X i < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < Y i)
    (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPdiag : 1 / (j : ℝ) ≤ ((P ProjectionCocycleWindow.basisZero) 0).re)
    (hQdiag : ((Q ProjectionCocycleWindow.basisZero) 0).re ≤ 1 - 1 / (j : ℝ)) :
    p.ε j ≤ ∑ n ∈ Finset.range (2 * p.K j + 1),
      ‖FiniteWindow.convolution (p.K j)
        (fun v => (P ProjectionCocycleWindow.basisZero) v /
          (p.floorCocycle θ v (MixedRadix.circleValue d) : ℂ))
        (fun v => (p.floorCocycle θ (-v) (MixedRadix.circleValue e) : ℂ) *
          conj (((1 - Q) ProjectionCocycleWindow.basisZero) (-v))) n‖ := by
  have hexcl := hp.source_good_event_exclusions j hj d e hd he X Y hX hY
    hdigit hedigit hcurrent hfuture
  exact hp.canonical_projection_convolution_lower j hj _ _
    (fun s hs i hi => (hexcl s hs i hi).1)
    (fun s hs i hi => (hexcl s hs i hi).2) P Q hP hQ hPdiag hQdiag

theorem canonical_projection_integral_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (j : ℕ) (hj : 1 ≤ j) (E : Set Ω) (x y : Ω → Circle)
    (hx : Measurable x) (hy : Measurable y)
    (P Q : Ω → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hPm : StronglyMeasurable (fun ω => P ω ProjectionCocycleWindow.basisZero))
    (hQm : StronglyMeasurable (fun ω => Q ω ProjectionCocycleWindow.basisZero))
    (hP : ∀ ω, IsStarProjection (P ω)) (hQ : ∀ ω, IsStarProjection (Q ω))
    (hE : ∀ᵐ ω ∂μ.restrict E,
      (∀ s, j ≤ s → ∀ i ∈ p.block s,
        p.coordinate i (x ω) < 1 - 2 * (p.K j : ℝ) / p.N s) ∧
      (∀ s, j ≤ s → ∀ i ∈ p.block s,
        2 * (p.K j : ℝ) / p.N s < p.coordinate i (y ω)) ∧
      1 / (j : ℝ) ≤ ((P ω ProjectionCocycleWindow.basisZero) 0).re ∧
      ((Q ω ProjectionCocycleWindow.basisZero) 0).re ≤ 1 - 1 / (j : ℝ)) :
    p.ε j * μ.real E ≤ ∫ ω in E, ∑ n ∈ Finset.range (2 * p.K j + 1),
      ‖FiniteWindow.convolution (p.K j)
        (fun v => (P ω ProjectionCocycleWindow.basisZero) v /
          (p.floorCocycle θ v (x ω) : ℂ))
        (fun v => (p.floorCocycle θ (-v) (y ω) : ℂ) *
          conj (((1 - Q ω) ProjectionCocycleWindow.basisZero) (-v))) n‖ ∂μ := by
  let A : Ω → ℤ → ℂ := fun ω v =>
    (P ω ProjectionCocycleWindow.basisZero) v / (p.floorCocycle θ v (x ω) : ℂ)
  let B : Ω → ℤ → ℂ := fun ω v =>
    (p.floorCocycle θ (-v) (y ω) : ℂ) *
      conj (((1 - Q ω) ProjectionCocycleWindow.basisZero) (-v))
  have hγ : StronglyMeasurable (fun ω => (1 - Q ω) ProjectionCocycleWindow.basisZero) := by
    have hbase : StronglyMeasurable
        ((fun _ : Ω => ProjectionCocycleWindow.basisZero) -
          fun ω => Q ω ProjectionCocycleWindow.basisZero) :=
      stronglyMeasurable_const.sub hQm
    convert hbase using 1
    funext ω
    simp only [Pi.sub_apply, sub_apply, one_apply_eq_self]
  have hA : ∀ v, Measurable (fun ω => A ω v) := by
    intro v
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 v).continuous.comp_stronglyMeasurable hPm).measurable.div
      (Complex.continuous_ofReal.measurable.comp ((hp.measurable_parameter_cocycle v).comp hx))
  have hB : ∀ v, Measurable (fun ω => B ω v) := by
    intro v
    exact (Complex.continuous_ofReal.measurable.comp
      ((hp.measurable_parameter_cocycle (-v)).comp hy)).mul
      (Complex.continuous_conj.measurable.comp
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-v)).continuous.comp_stronglyMeasurable hγ).measurable)
  apply FiniteWindow.integral_lower_of_sum_bound μ (p.K j)
    (p.coefficientBound j) (1 / (j : ℝ)) (p.ε j)
    (hp.parameter_convolution_sum_lower j hj) E A B hA hB
  filter_upwards [hE] with ω hω
  exact hp.canonical_projection_coefficient_properties j hj (x ω) (y ω)
    hω.1 hω.2.1 (P ω) (Q ω) (hP ω) (hQ ω) (1 / (j : ℝ))
    hω.2.2.1 hω.2.2.2

end Invariant233.CircleParameterLaws

end

end OAI
