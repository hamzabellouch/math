import OAI.Probability.FreeIsing.Conditioning.SideSignalLoss

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

lemma condExp_cavity_attenuation_le_of_condIndep
    {Ω S B : Type*} {mΩ : MeasurableSpace Ω} {mS : MeasurableSpace S}
    {mB : MeasurableSpace B} [StandardBorelSpace Ω] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρsym : MeasurePreserving Neg.neg ρ ρ)
    {latent : Ω → S} {X : Ω → B} {Y : Ω → ℝ} {shift : B → ℝ} {eta : S → ℝ}
    (hS : Measurable latent) (hX : Measurable X) (hY : Measurable Y)
    (hs : Measurable shift) (hInd : X ⟂ᵢ[latent, hS; μ] Y)
    (hη : ∀ᵐ w ∂μ, |eta (latent w)| ≤ 1)
    (hLaw : ∀ᵐ w ∂μ, condDistrib Y latent μ (latent w) =
      linearSignalTilt ρ Real.tanh (eta (latent w) * theta)) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta
        (shift (X v) + cavityMessage theta (Y v)) ^ 2 | mB.comap X]) w ≤
          1 - sideSignalLossCoefficient theta * (∫ y, Real.tanh y ^ 2 ∂ρ) := by
  have hPair := hS.prodMk hX
  have hIndLaw :=
    (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hS).mp hInd
  have hIndAE := ae_of_ae_map hPair.aemeasurable hIndLaw
  have hLawPair : ∀ᵐ w ∂μ,
      condDistrib Y (fun v => (latent v, X v)) μ (latent w, X w) =
        linearSignalTilt ρ Real.tanh (eta (latent w) * theta) := by
    filter_upwards [hIndAE, hLaw] with w hw hLaww
    exact hw.trans hLaww
  have hFine := condExp_cavity_attenuation_le_of_tiltLaw
    (X := fun w => (latent w, X w)) (Y := Y)
    (shift := fun p : S × B => shift p.2) (eta := fun p : S × B => eta p.1)
    hθ0 hθ1 hρsym hPair hY (hs.comp measurable_snd) hη hLawPair
  have hcoarse : mB.comap X ≤
      (inferInstance : MeasurableSpace (S × B)).comap (fun w => (latent w, X w)) := by
    have h := MeasurableSpace.comap_mono (g := fun w => (latent w, X w))
      (measurable_snd : Measurable (Prod.snd : S × B → B)).comap_le
    simpa only [MeasurableSpace.comap_comp, Function.comp_def] using h
  let q : ℝ := 1 - sideSignalLossCoefficient theta * (∫ y, Real.tanh y ^ 2 ∂ρ)
  have hmono := condExp_mono (m := mB.comap X)
    integrable_condExp (integrable_const q) hFine
  rw [condExp_const hX.comap_le q] at hmono
  have htower := condExp_condExp_of_le (μ := μ)
    (f := fun v => responseAttenuation theta
      (shift (X v) + cavityMessage theta (Y v)) ^ 2) hcoarse hPair.comap_le
  filter_upwards [hmono, htower] with w hw htw
  rw [htw] at hw
  exact hw

end Problem367

end

end OAI
