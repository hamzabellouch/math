import OAI.Probability.StrongRayleigh.CylindricalIndependence
import OAI.Probability.StrongRayleigh.FiniteGaussianCharacteristic

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Problem336AdditiveD139.CharacteristicLaw

theorem gaussian_field_law_and_independent_of_event_characteristic
    {Ω : Type u_1} {I : Type u_2} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → I → ℝ) (hD : Measurable D) (v : ℝ≥0)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ S : Finset I, ∀ θ : S → ℝ,
      (∫ ω in A, Complex.exp (((∑ i : S, D ω i * θ i : ℝ) : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) *
          Complex.exp (((-(v : ℝ) * ∑ i : S, θ i ^ 2) / 2 : ℝ) : ℂ)) :
    Measure.map D μ = Measure.infinitePi (fun _ : I => gaussianReal 0 v) ∧
      Indep m (MeasurableSpace.comap D inferInstance) μ := by
  apply CylindricalIndependence.product_law_and_indep_of_finite_restrictions m μ
    (fun _ : I => gaussianReal 0 v) D hD
  intro S
  apply gaussian_pi_law_and_independent_of_event_characteristic
    ((Finset.measurable_restrict S).comp hD) hm v
  intro A hA θ
  exact hchar A hA S θ

end Problem336AdditiveD139.CharacteristicLaw

end

end OAI
