import OAI.Probability.StrongRayleigh.InnovationFiniteLaw
import OAI.Probability.StrongRayleigh.InnovationPathCriterion

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139

theorem independent_preBrownian_of_local_characteristic
    {Ω : Type u_1} {I : Type u_2} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hlocal : ∀ (S : Finset I) (θ : S → ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ≥0, u ≤ v → (v : ℝ) - u ≤ 1 → ∀ᵐ ω ∂P,
        ‖P[fun ω => Complex.exp (Complex.I *
          ((∑ i : S, θ i * (X i v ω - X i u ω) : ℝ) : ℂ)) | H u] ω -
          (Real.exp (-((v : ℝ) - u) * (∑ i : S, θ i ^ 2) / 2) : ℂ)‖ ≤
            C * ((v : ℝ) - u) * Real.sqrt ((v : ℝ) - u)) :
    (∀ i, IsPreBrownianReal (X i) P) ∧
      iIndepFun (fun i ω t => X i t ω) P := by
  classical
  have hresult (S : Finset I) (u v : ℝ≥0) (huv : u ≤ v) :=
    InnovationCharacteristic.gaussian_increment_law_of_local_characteristic_nnreal
      (fun t => H t) (fun _ _ h => H.mono h) H.le (fun t ω (i : S) => X i t ω)
      (fun t i => (hX i t).stronglyMeasurable)
      (fun θ => by
        simpa only [InnovationCharacteristic.phase, mul_comm] using hlocal S θ) huv
  apply independent_preBrownian_of_adapted_gaussian_increments H hX hzero
  · intro S u v huv
    refine ⟨?_, (hresult S u v huv).1⟩
    exact (Measurable.of_eval fun (i : S) =>
      ((hX i).measurable (i := v)).sub ((hX i).measurable (i := u))).aemeasurable
  · intro S u v huv
    exact (hresult S u v huv).2.symm

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

theorem exists_iid_path_version_of_local_characteristic
    {Ω : Type u_3} {I : Type u_4} [mΩ : MeasurableSpace Ω] [Countable I]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure C(ℝ≥0, ℝ))
    (hν : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ν)
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => X i t ω))
    (hlocal : ∀ (S : Finset I) (θ : S → ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ≥0, u ≤ v → (v : ℝ) - u ≤ 1 → ∀ᵐ ω ∂P,
        ‖P[fun ω => Complex.exp (Complex.I *
          ((∑ i : S, θ i * (X i v ω - X i u ω) : ℝ) : ℂ)) | H u] ω -
          (Real.exp (-((v : ℝ) - u) * (∑ i : S, θ i ^ 2) / 2) : ℂ)‖ ≤
            C * ((v : ℝ) - u) * Real.sqrt ((v : ℝ) - u)) :
    ∃ W : Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W P = Measure.infinitePi (fun _ : I => ν) ∧
      ∀ᵐ ω ∂P, ∀ i t, W ω i t = X i t ω := by
  obtain ⟨hpre, hindep⟩ :=
    independent_preBrownian_of_local_characteristic H hX hzero hlocal
  exact exists_measurable_iid_brownian_path_version ν hν hpre hindep hcont

end Problem336AdditiveD139

end

end OAI
