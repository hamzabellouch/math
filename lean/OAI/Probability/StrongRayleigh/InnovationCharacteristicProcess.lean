import OAI.Probability.StrongRayleigh.InnovationProcessLaw
import OAI.Probability.StrongRayleigh.FiniteGaussianCharacteristic

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139

theorem independent_preBrownian_of_eventwise_characteristic
    {Ω : Type u_1} {I : Type u_2} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hchar : ∀ (S : Finset I) (u v : ℝ≥0), u ≤ v →
      ∀ A : Set Ω, MeasurableSet[H u] A → ∀ θ : S → ℝ,
        (∫ ω in A, Complex.exp
          (((∑ i : S, θ i * (X i v ω - X i u ω) : ℝ) : ℂ) * Complex.I) ∂P) =
          ((P A).toReal : ℂ) * Complex.exp
            (- ((v - u : ℝ≥0) : ℂ) * ((∑ i : S, θ i ^ 2 : ℝ) : ℂ) / 2)) :
    (∀ i, IsPreBrownianReal (X i) P) ∧
      iIndepFun (fun i ω t => X i t ω) P := by
  classical
  have hmeas (S : Finset I) (u v : ℝ≥0) :
      Measurable (fun ω (i : S) => X i v ω - X i u ω) :=
    Measurable.of_eval fun i => (hX i).measurable.sub (hX i).measurable
  have hresult (S : Finset I) (u v : ℝ≥0) (huv : u ≤ v) :
      Measure.map (fun ω (i : S) => X i v ω - X i u ω) P =
          Measure.pi (fun _ : S => gaussianReal 0 (v - u)) ∧
        Indep (H u) (MeasurableSpace.comap
          (fun ω (i : S) => X i v ω - X i u ω) inferInstance) P := by
    apply CharacteristicLaw.gaussian_pi_law_and_independent_of_event_characteristic
      (hmeas S u v) (H.le u) (v - u)
    intro A hA θ
    simpa only [mul_comm, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_ofNat] using hchar S u v huv A hA θ
  apply independent_preBrownian_of_adapted_gaussian_increments H hX hzero
  · intro S u v huv
    exact ⟨(hmeas S u v).aemeasurable, (hresult S u v huv).1⟩
  · intro S u v huv
    exact (hresult S u v huv).2.symm

end Problem336AdditiveD139

end

end OAI
