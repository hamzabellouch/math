import OAI.Geometry.RCD.Heat.LogarithmicEnergyIdentity
import OAI.Geometry.RCD.Heat.LocalLogarithmicFluxBound
import OAI.Geometry.RCD.Sobolev.LocalProbabilityEnergy
import OAI.Geometry.RCD.Heat.OsmoticNoiseRate
import OAI.Geometry.RCD.Heat.ScaledLiYauRemainder

namespace OAI

/-! # The localized osmotic estimate with an explicit vanishing-noise rate -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localized_osmotic_noise_rate {Ω : Set X} (hΩ : MeasurableSet Ω)
    (φ F G : X → ℝ) (hφ : ∀ x, φ x ∈ Icc (0:ℝ) 1) (hs : ∀ x ∉ Ω, φ x=0)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (hF : ∀ x ∈ Ω, 0<F x) (hG : ∀ x ∈ Ω, 0<G x)
    {A B : ℝ} (hFB : ∀ᵐ x ∂μ, |F x| ≤ A) (hGB : ∀ᵐ x ∂μ, |G x| ≤ B)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (F x*G x)))]
    (u v U V w : SobolevSpace μ Q)
    (hU : ∀ z, localGamma μ Q U z =ᵐ[μ.restrict Ω] fun x => localGamma μ Q u z x/F x)
    (hV : ∀ z, localGamma μ Q V z =ᵐ[μ.restrict Ω] fun x => localGamma μ Q v z x/G x)
    (hiu : Integrable (fun x => φ x*(G x/F x)*localGamma μ Q u u x) μ)
    (hiv : Integrable (fun x => φ x*(F x/G x)*localGamma μ Q v v x) μ)
    (hie : Integrable (fun x => φ x*localGamma μ Q u v x) μ)
    {c δ a b N k Lv Lo M : ℝ} (hc : 0<c) (hc1 : c≤1) (hδ : 0<δ)
    (ha : δ≤a) (hb : δ≤b) (hN : 0≤N) (hk : 0≤k)
    (hLo : 0≤Lo) (hM : 0≤M)
    (hvel : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q (c • (V-U)) x≤Lv)
    (hosm : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q (c • (U+V)) x≤Lo)
    (hwM : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q w x≤M)
    (hw : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q w x=0)
    (hest :
      let S := (∫ x, φ x*(G x/F x)*localGamma μ Q u u x ∂μ)+
        (∫ x, φ x*(F x/G x)*localGamma μ Q v v x ∂μ)
      let E := weightedGamma μ Q φ u v
      let J := weightedGamma μ Q G u w+weightedGamma μ Q F v w
      let R := (N*(1+c)^2/2)*(2*k/c+1/(c*a)+1/(c*b))*(∫ x, φ x*(F x*G x) ∂μ)
      S+2*E ≤ (c/(2+c))*(S-2*E)+(2/(2+c))*(R-(1+c)*J)) :
    weightedGamma μ Q (fun x => φ x*(F x*G x)) (c • (U+V)) (c • (U+V)) ≤
      c*(Lv^2+4*N*k+4*N/δ+2*(Lo*M)) := by
  let S := (∫ x, φ x*(G x/F x)*localGamma μ Q u u x ∂μ)+
    (∫ x, φ x*(F x/G x)*localGamma μ Q v v x ∂μ)
  let E := weightedGamma μ Q φ u v
  let J := weightedGamma μ Q G u w+weightedGamma μ Q F v w
  let R := (N*(1+c)^2/2)*(2*k/c+1/(c*a)+1/(c*b))*(∫ x, φ x*(F x*G x) ∂μ)
  have hplus : weightedGamma μ Q (fun x => φ x*(F x*G x)) (c • (U+V)) (c • (U+V)) =
      c^2*(S+2*E) := by
    simpa only [S,E,one_pow,one_mul,mul_one,one_smul,add_comm V U] using
      logarithmic_energy_identity μ Q hΩ φ F G hs hF hG u v U V 1 c hU hV hiu hiv hie
  have hminus : weightedGamma μ Q (fun x => φ x*(F x*G x)) (c • (V-U)) (c • (V-U)) =
      c^2*(S-2*E) := by
    simpa only [S,E,neg_one_sq,one_mul,neg_one_smul,sub_eq_add_neg,mul_neg_one,neg_mul] using
      logarithmic_energy_identity μ Q hΩ φ F G hs hF hG u v U V (-1) c hU hV hiu hiv hie
  have hVB : c^2*(S-2*E)≤Lv^2 := by
    rw [← hminus]
    exact (local_probability_energy_bound μ Q hΩ (fun x => F x*G x) φ (hFm.mul hGm)
      (fun x => mul_nonneg (hF0 x) (hG0 x)) hφ hs _ hvel).2
  have hmass := probability_cutoff_mass μ (fun x => F x*G x) φ (hFm.mul hGm)
    (fun x => mul_nonneg (hF0 x) (hG0 x)) hφ
  have hRB : c^2*R≤c*(4*N*k+4*N/δ) :=
    scaled_liYau_remainder_le hc hc1 hδ ha hb hN hk hmass.1 hmass.2
  have hJB : |c*J|≤Lo*M := local_logarithmic_flux_bound μ Q hΩ F G hFm hGm hF0 hG0
    hF hG hFB hGB u v U V w c (hU w) (hV w) hLo hosm hwM hw
  rw [hplus]
  calc
    _ ≤ c*(Lv^2+(4*N*k+4*N/δ)+2*(Lo*M)) :=
      osmotic_noise_rate hc hc1 (sq_nonneg Lv) (by positivity) (mul_nonneg hLo hM)
        hVB hRB hJB hest
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
