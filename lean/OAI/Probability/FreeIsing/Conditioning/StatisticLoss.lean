import OAI.Probability.FreeIsing.Gaussian.ComponentSignalAttenuation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem condExp_statistic_attenuation_le_of_tiltLaw
    {Ω B : Type*} {mΩ : MeasurableSpace Ω} {mB : MeasurableSpace B}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρsym : MeasurePreserving Neg.neg ρ ρ) (hρbound : ∀ᵐ q ∂ρ, |q| ≤ 1)
    {X : Ω → B} {Q : Ω → ℝ} {shift eta : B → ℝ}
    (hX : Measurable X) (hQ : Measurable Q) (hs : Measurable shift)
    (hη : ∀ᵐ w ∂μ, |eta (X w)| ≤ 1)
    (hLaw : ∀ᵐ w ∂μ, condDistrib Q X μ (X w) =
      linearSignalTilt ρ id (eta (X w) * theta)) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
          1 - sideSignalLossCoefficient theta * (∫ q, q ^ 2 ∂ρ) := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  let F : B × ℝ → ℝ := fun p =>
    responseAttenuation theta (shift p.1 + statisticMessage theta p.2) ^ 2
  have hFm : Measurable F :=
    ((continuous_responseAttenuation hθsq).measurable.comp
      ((hs.comp measurable_fst).add
        ((measurable_statisticMessage theta).comp measurable_snd))).pow_const 2
  have hFi : Integrable (fun w => F (X w, Q w)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (hFm.comp (hX.prodMk hQ)).aestronglyMeasurable
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := responseAttenuation_pos hθsq
      (shift (X w) + statisticMessage theta (Q w))
    have hle := responseAttenuation_le_one hθsq
      (shift (X w) + statisticMessage theta (Q w))
    change responseAttenuation theta (shift (X w) + statisticMessage theta (Q w)) ^ 2 ≤ 1
    nlinarith
  have hCE := condExp_prod_ae_eq_integral_condDistrib hX hQ.aemeasurable
    hFm.stronglyMeasurable hFi
  filter_upwards [hCE, hη, hLaw] with w hw hηw hLaww
  change (μ[fun v => F (X v, Q v) | mB.comap X]) w ≤ _
  rw [hw, hLaww]
  exact integral_tilted_statistic_attenuation_le hθ0 hθ1 hηw measurable_id hρbound
    (MeasurableEquiv.neg ℝ) hρsym (Filter.Eventually.of_forall fun _ => rfl) (shift (X w))

theorem condExp_statistic_attenuation_le_of_condIndep
    {Ω S B : Type*} {mΩ : MeasurableSpace Ω} {mS : MeasurableSpace S}
    {mB : MeasurableSpace B} [StandardBorelSpace Ω] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρsym : MeasurePreserving Neg.neg ρ ρ) (hρbound : ∀ᵐ q ∂ρ, |q| ≤ 1)
    {latent : Ω → S} {X : Ω → B} {Q : Ω → ℝ} {shift : B → ℝ} {eta : S → ℝ}
    (hS : Measurable latent) (hX : Measurable X) (hQ : Measurable Q)
    (hs : Measurable shift) (hInd : X ⟂ᵢ[latent, hS; μ] Q)
    (hη : ∀ᵐ w ∂μ, |eta (latent w)| ≤ 1)
    (hLaw : ∀ᵐ w ∂μ, condDistrib Q latent μ (latent w) =
      linearSignalTilt ρ id (eta (latent w) * theta)) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
          1 - sideSignalLossCoefficient theta * (∫ q, q ^ 2 ∂ρ) := by
  have hPair := hS.prodMk hX
  have hIndLaw :=
    (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hQ hX hS).mp hInd
  have hIndAE := ae_of_ae_map hPair.aemeasurable hIndLaw
  have hLawPair : ∀ᵐ w ∂μ,
      condDistrib Q (fun v => (latent v, X v)) μ (latent w, X w) =
        linearSignalTilt ρ id (eta (latent w) * theta) := by
    filter_upwards [hIndAE, hLaw] with w hw hLaww
    exact hw.trans hLaww
  have hFine := condExp_statistic_attenuation_le_of_tiltLaw
    (X := fun w => (latent w, X w)) (Q := Q)
    (shift := fun p : S × B => shift p.2) (eta := fun p : S × B => eta p.1)
    hθ0 hθ1 hρsym hρbound hPair hQ (hs.comp measurable_snd) hη hLawPair
  have hcoarse : mB.comap X ≤
      (inferInstance : MeasurableSpace (S × B)).comap (fun w => (latent w, X w)) := by
    have h := MeasurableSpace.comap_mono (g := fun w => (latent w, X w))
      (measurable_snd : Measurable (Prod.snd : S × B → B)).comap_le
    simpa only [MeasurableSpace.comap_comp, Function.comp_def] using h
  let q : ℝ := 1 - sideSignalLossCoefficient theta * (∫ q, q ^ 2 ∂ρ)
  have hmono := condExp_mono (m := mB.comap X)
    integrable_condExp (integrable_const q) hFine
  rw [condExp_const hX.comap_le q] at hmono
  have htower := condExp_condExp_of_le (μ := μ)
    (f := fun v => responseAttenuation theta
      (shift (X v) + statisticMessage theta (Q v)) ^ 2) hcoarse hPair.comap_le
  filter_upwards [hmono, htower] with w hw htw
  rw [htw] at hw
  exact hw

namespace ComponentSignalAttenuation

theorem condExp_attenuation_le_critical_of_condIndep
    {d : ℕ} {theta : ℝ} {ν : Measure (TreeVertex d → IsingSpin)}
    (hν : HasFreeIsingLaw theta ν) (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    {Ω S B : Type*} {mΩ : MeasurableSpace Ω} {mS : MeasurableSpace S}
    {mB : MeasurableSpace B} [StandardBorelSpace Ω] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {latent : Ω → S} {X : Ω → B} {Q : Ω → ℝ} {shift : B → ℝ} {eta : S → ℝ}
    (hS : Measurable latent) (hX : Measurable X) (hQ : Measurable Q)
    (hs : Measurable shift) (hInd : X ⟂ᵢ[latent, hS; μ] Q)
    (hη : ∀ᵐ w ∂μ, |eta (latent w)| ≤ 1)
    (hLaw : ∀ᵐ w ∂μ, condDistrib Q latent μ (latent w) =
      linearSignalTilt (posteriorLaw ν c t) id (eta (latent w) * theta)) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
          1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  let := posteriorLaw_probability hν c t
  have h := condExp_statistic_attenuation_le_of_condIndep hθ0.le hθ1
    (posteriorLaw_neg_invariant hν c t) (posteriorLaw_abs_le_one ν c t)
    hS hX hQ hs hInd hη hLaw
  have hm := posteriorLaw_information_lower hν (by linarith) hθ1.le c hcritical ht
  have hc := sideSignalLossCoefficient_pos hθ0 hθ1
  have hω : 0 ≤ min (Real.sqrt (t : ℝ)) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  have hco := mul_le_mul_of_nonneg_right
    (show lossCoefficient theta ≤ sideSignalLossCoefficient theta / 5 from min_le_left _ _) hω
  have hmul := mul_le_mul_of_nonneg_left hm hc.le
  filter_upwards [h] with w hw
  nlinarith

end ComponentSignalAttenuation

end Problem367

end

end OAI
