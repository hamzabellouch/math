import OAI.Probability.InvariantIsing.Cavity.CavityProjectedSpin
import OAI.Probability.InvariantIsing.Fields.FieldEnergyCoordinates

namespace OAI

/-! Removing the ordinary Gaussian residual while retaining the leaf and spin. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal NNReal

namespace InvariantIsing

private lemma cavity_tilt_marginal {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (μ : Measure Y) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (F : X × Y → ℝ) (f : X → ℝ) (hF : Measurable F) (hf : Measurable f)
    (hI : Integrable (fun p => Real.exp (F p)) (ν.prod μ))
    (hi : ∀ x, Integrable (fun y => Real.exp (F (x, y))) μ)
    (he : ∀ x, (∫ y, Real.exp (F (x, y)) ∂μ) = Real.exp (f x)) :
    ((ν.prod μ).tilted F).map Prod.fst = ν.tilted f := by
  have hden : (∫ p, Real.exp (F p) ∂ν.prod μ) = ∫ x, Real.exp (f x) ∂ν := by
    rw [integral_prod _ hI]
    simp_rw [he]
  have hd : 0 < ∫ x, Real.exp (f x) ∂ν := by
    rw [← hden]
    exact integral_exp_pos hI
  have hslice (x : X) :
      (∫⁻ y, ENNReal.ofReal (Real.exp (F (x, y))) ∂μ) = ENNReal.ofReal (Real.exp (f x)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi x)
      (ae_of_all _ fun y => (Real.exp_pos _).le), he]
  unfold Measure.tilted
  rw [hden]
  apply Measure.ext_of_lintegral
  intro g hg
  have hw : Measurable (fun p : X × Y =>
      ENNReal.ofReal (Real.exp (F p) / ∫ x, Real.exp (f x) ∂ν)) :=
    (hF.exp.div_const _).ennreal_ofReal
  have ha : Measurable (fun x : X =>
      ENNReal.ofReal (Real.exp (f x) / ∫ x, Real.exp (f x) ∂ν)) :=
    (hf.exp.div_const _).ennreal_ofReal
  have hmul : Measurable (fun p : X × Y =>
      ENNReal.ofReal (Real.exp (F p) / ∫ x, Real.exp (f x) ∂ν) * g p.1) :=
    hw.mul (hg.comp measurable_fst)
  rw [lintegral_map hg measurable_fst,
    lintegral_withDensity_eq_lintegral_mul _ hw
      (show Measurable (fun p : X × Y => g p.1) from hg.comp measurable_fst),
    lintegral_withDensity_eq_lintegral_mul _ ha hg]
  change (∫⁻ p : X × Y, ENNReal.ofReal (Real.exp (F p) / ∫ x, Real.exp (f x) ∂ν) *
    g p.1 ∂ν.prod μ) = _
  rw [lintegral_prod _ hmul.aemeasurable]
  apply lintegral_congr_ae
  apply ae_of_all
  intro x
  simp only [div_eq_mul_inv, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [mul_assoc]
  have hx : Measurable (fun y : Y => ENNReal.ofReal (Real.exp (F (x, y)))) :=
    ((hF.comp (measurable_const.prodMk measurable_id)).exp.ennreal_ofReal)
  rw [lintegral_mul_const _ hx, hslice]
  simpa only [Pi.mul_apply] using (mul_assoc (ENNReal.ofReal (Real.exp (f x)))
    (ENNReal.ofReal ((∫ x, Real.exp (f x) ∂ν)⁻¹)) (g x)).symm

theorem cavity_field_residual_marginal {X : Type*} [MeasurableSpace X] {N : ℕ}
    (ν : Measure X) [IsProbabilityMeasure ν]
    (z : X → Fin N → ℝ) (hz : Measurable z)
    (ε : X → Spin N) (hε : Measurable ε) (v : ℝ≥0) (c : ℝ)
    (hI : Integrable (fun p : X × (Fin N → ℝ) =>
      Real.exp (fieldEnergy (z p.1 + p.2) (ε p.1) + (N : ℝ) * c / 2))
      (ν.prod (vectorGaussianLaw N v))) :
    ((ν.prod (vectorGaussianLaw N v)).tilted
      (fun p => fieldEnergy (z p.1 + p.2) (ε p.1) + (N : ℝ) * c / 2)).map Prod.fst =
      ν.tilted (fun x => fieldEnergy (z x) (ε x) + (N : ℝ) * (c + v) / 2) := by
  have henergy : Measurable (fun p : (Fin N → ℝ) × Spin N => fieldEnergy p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact (measurable_pi_apply σ).comp (measurable_fieldEnergy_map N)
  have hz' : Measurable (fun p : X × (Fin N → ℝ) => z p.1 + p.2) :=
    (hz.comp measurable_fst).add measurable_snd
  have hε' : Measurable (fun p : X × (Fin N → ℝ) => ε p.1) := hε.comp measurable_fst
  have hF : Measurable (fun p : X × (Fin N → ℝ) =>
      fieldEnergy (z p.1 + p.2) (ε p.1) + (N : ℝ) * c / 2) := by
    exact (henergy.comp (hz'.prodMk hε')).add_const _
  have hf : Measurable (fun x : X => fieldEnergy (z x) (ε x) + (N : ℝ) * (c + v) / 2) := by
    exact (henergy.comp (hz.prodMk hε)).add_const _
  have hi (x : X) : Integrable (fun y : Fin N → ℝ =>
      Real.exp (fieldEnergy (z x + y) (ε x) + (N : ℝ) * c / 2))
      (vectorGaussianLaw N v : Measure (Fin N → ℝ)) :=
    cavity_residual_spin_integrable (n := N) v c (z x) (ε x)
  have he (x : X) : (∫ y : Fin N → ℝ,
      Real.exp (fieldEnergy (z x + y) (ε x) + (N : ℝ) * c / 2)
      ∂(vectorGaussianLaw N v : Measure (Fin N → ℝ))) =
        Real.exp (fieldEnergy (z x) (ε x) + (N : ℝ) * (c + v) / 2) :=
    cavity_residual_spin_integral (n := N) v c (z x) (ε x)
  have hmap := cavity_tilt_marginal (X := X) (Y := Fin N → ℝ) ν
    (vectorGaussianLaw N v : Measure (Fin N → ℝ))
    (fun p : X × (Fin N → ℝ) => fieldEnergy (z p.1 + p.2) (ε p.1) + (N : ℝ) * c / 2)
    (fun x : X => fieldEnergy (z x) (ε x) + (N : ℝ) * (c + v) / 2) hF hf hI hi he
  exact hmap

end InvariantIsing

end

end OAI
