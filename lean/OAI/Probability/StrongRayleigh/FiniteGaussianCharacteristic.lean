import OAI.Probability.StrongRayleigh.CharacteristicLaw

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem336AdditiveD139.CharacteristicLaw

variable {F : Type u_1} [Fintype F]

theorem charFun_pi_centered_gaussian (v : ℝ≥0) (t : EuclideanSpace ℝ F) :
    charFun ((Measure.pi (fun _ : F => gaussianReal 0 v)).map (WithLp.toLp 2)) t =
      Complex.exp (((-(v : ℝ) * ∑ i : F, (t i) ^ 2) / 2 : ℝ) : ℂ) := by
  rw [charFun_pi]
  simp_rw [charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

variable {Ω : Type u_2} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → F → ℝ}

theorem map_restrict_eq_gaussian_pi_of_characteristic
    (hZ : Measurable Z) (v : ℝ≥0) (A : Set Ω)
    (hchar : ∀ t : F → ℝ,
      (∫ ω in A, Complex.exp (((∑ i : F, Z ω i * t i : ℝ) : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) *
          Complex.exp (((-(v : ℝ) * ∑ i : F, (t i) ^ 2) / 2 : ℝ) : ℂ)) :
    Measure.map Z (μ.restrict A) = μ A • Measure.pi (fun _ : F => gaussianReal 0 v) := by
  let e : (F → ℝ) ≃ᵐ EuclideanSpace ℝ F := MeasurableEquiv.toLp 2 (F → ℝ)
  apply e.map_measurableEquiv_injective
  rw [Measure.map_map e.measurable hZ, Measure.map_smul _ e.measurable.aemeasurable]
  apply map_restrict_eq_smul_of_characteristic (e.measurable.comp hZ) A
  intro t
  rw [show Measure.map e (Measure.pi (fun _ : F => gaussianReal 0 v)) =
    (Measure.pi (fun _ : F => gaussianReal 0 v)).map (WithLp.toLp 2) from rfl,
    charFun_pi_centered_gaussian]
  simpa only [Function.comp_apply, e, MeasurableEquiv.coe_toLp,
    PiLp.inner_apply, Real.inner_apply, mul_comm] using hchar t

theorem gaussian_pi_law_and_independent_of_event_characteristic
    [IsProbabilityMeasure μ] (hZ : Measurable Z) (hm : m ≤ mΩ) (v : ℝ≥0)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ t : F → ℝ,
      (∫ ω in A, Complex.exp (((∑ i : F, Z ω i * t i : ℝ) : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) *
          Complex.exp (((-(v : ℝ) * ∑ i : F, (t i) ^ 2) / 2 : ℝ) : ℂ)) :
    Measure.map Z μ = Measure.pi (fun _ : F => gaussianReal 0 v) ∧
      Indep m (MeasurableSpace.comap Z inferInstance) μ := by
  have hr (A : Set Ω) (hA : MeasurableSet[m] A) :=
    map_restrict_eq_gaussian_pi_of_characteristic hZ v A (hchar A hA)
  have hlaw : Measure.map Z μ = Measure.pi (fun _ : F => gaussianReal 0 v) := by
    simpa using hr Set.univ MeasurableSet.univ
  exact ⟨hlaw, independent_of_restricted_law hZ hm hlaw hr⟩

end Problem336AdditiveD139.CharacteristicLaw

end

end OAI
