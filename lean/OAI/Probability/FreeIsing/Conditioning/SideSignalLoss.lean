import OAI.Probability.FreeIsing.Gaussian.SideSignalLoss

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω B : Type*} {mΩ : MeasurableSpace Ω} {mB : MeasurableSpace B}
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma condExp_cavity_attenuation_le_of_tiltLaw
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρsym : MeasurePreserving Neg.neg ρ ρ)
    {X : Ω → B} {Y : Ω → ℝ} {shift eta : B → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hs : Measurable shift)
    (hη : ∀ᵐ w ∂μ, |eta (X w)| ≤ 1)
    (hLaw : ∀ᵐ w ∂μ, condDistrib Y X μ (X w) =
      linearSignalTilt ρ Real.tanh (eta (X w) * theta)) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta
        (shift (X v) + cavityMessage theta (Y v)) ^ 2 | mB.comap X]) w ≤
          1 - sideSignalLossCoefficient theta * (∫ y, Real.tanh y ^ 2 ∂ρ) := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  let F : B × ℝ → ℝ := fun p =>
    responseAttenuation theta (shift p.1 + cavityMessage theta p.2) ^ 2
  have hψ : Measurable (cavityMessage theta) :=
    (lipschitzWith_cavityMessage hθ0 hθ1.le).continuous.measurable
  have hFm : Measurable F :=
    ((continuous_responseAttenuation hθsq).measurable.comp
      ((hs.comp measurable_fst).add (hψ.comp measurable_snd))).pow_const 2
  have hFi : Integrable (fun w => F (X w, Y w)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (hFm.comp (hX.prodMk hY)).aestronglyMeasurable
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := responseAttenuation_pos hθsq
      (shift (X w) + cavityMessage theta (Y w))
    have hle := responseAttenuation_le_one hθsq
      (shift (X w) + cavityMessage theta (Y w))
    change responseAttenuation theta (shift (X w) + cavityMessage theta (Y w)) ^ 2 ≤ 1
    nlinarith
  have hCE := condExp_prod_ae_eq_integral_condDistrib hX hY.aemeasurable
    hFm.stronglyMeasurable hFi
  filter_upwards [hCE, hη, hLaw] with w hw hηw hLaww
  change (μ[fun v => F (X v, Y v) | mB.comap X]) w ≤ _
  rw [hw, hLaww]
  exact integral_tilted_cavity_attenuation_le hθ0 hθ1 hηw measurable_id
    (MeasurableEquiv.neg ℝ) hρsym (Filter.Eventually.of_forall fun _ => rfl) (shift (X w))

end Problem367

end

end OAI
