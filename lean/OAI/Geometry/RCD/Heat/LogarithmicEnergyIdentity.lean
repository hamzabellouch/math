import OAI.Geometry.RCD.Heat.LocalLogarithmGammaByValue
import OAI.Geometry.RCD.Sobolev.HessianVelocityPolarization

namespace OAI

/-! # Exact weighted energies of scaled logarithmic sums and differences -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localGamma_linear_square (u v : SobolevSpace μ Q) (a c : ℝ) :
    localGamma μ Q (c • (v+a • u)) (c • (v+a • u)) =ᵐ[μ]
      fun x => c^2*(a^2*localGamma μ Q u u x+localGamma μ Q v v x+
        2*a*localGamma μ Q u v x) := by
  filter_upwards [localGamma_smul_left μ Q c (v+a • u) (c • (v+a • u)),
    localGamma_smul_right μ Q c (v+a • u) (v+a • u),
    localGamma_add_left μ Q v (a • u) (v+a • u),
    localGamma_add_right μ Q v v (a • u),
    localGamma_add_right μ Q (a • u) v (a • u),
    localGamma_smul_right μ Q a v u,localGamma_smul_left μ Q a u v,
    localGamma_smul_left μ Q a u (a • u),localGamma_smul_right μ Q a u u,
    localGamma_comm μ Q v u] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
  rw [h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀]
  ring

omit [ProperSpace X] in
theorem local_logarithmic_grams {Ω : Set X} (F G : X → ℝ)
    (u v U V : SobolevSpace μ Q)
    (hU : ∀ w, localGamma μ Q U w =ᵐ[μ.restrict Ω]
      fun x => localGamma μ Q u w x/F x)
    (hV : ∀ w, localGamma μ Q V w =ᵐ[μ.restrict Ω]
      fun x => localGamma μ Q v w x/G x) :
    ∀ᵐ x ∂μ.restrict Ω,
      localGamma μ Q U U x=localGamma μ Q u u x/(F x)^2 ∧
      localGamma μ Q V V x=localGamma μ Q v v x/(G x)^2 ∧
      localGamma μ Q U V x=localGamma μ Q u v x/(F x*G x) := by
  filter_upwards [hU U,hU u,hV V,hV v,hU V,hV u,
    ae_restrict_of_ae (localGamma_comm μ Q u U),
    ae_restrict_of_ae (localGamma_comm μ Q v V),
    ae_restrict_of_ae (localGamma_comm μ Q u V),
    ae_restrict_of_ae (localGamma_comm μ Q v u)]
    with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
  rw [h₁,h₃,h₅,h₇,h₈,h₉,h₂,h₄,h₆,h₁₀]
  simp only [div_div,pow_two,mul_comm,eq_self,and_self]

theorem logarithmic_energy_identity {Ω : Set X} (hΩ : MeasurableSet Ω)
    (φ F G : X → ℝ) (hs : ∀ x ∉ Ω, φ x=0)
    (hF : ∀ x ∈ Ω, 0<F x) (hG : ∀ x ∈ Ω, 0<G x)
    (u v U V : SobolevSpace μ Q) (a c : ℝ)
    (hU : ∀ w, localGamma μ Q U w =ᵐ[μ.restrict Ω]
      fun x => localGamma μ Q u w x/F x)
    (hV : ∀ w, localGamma μ Q V w =ᵐ[μ.restrict Ω]
      fun x => localGamma μ Q v w x/G x)
    (hiu : Integrable (fun x => φ x*(G x/F x)*localGamma μ Q u u x) μ)
    (hiv : Integrable (fun x => φ x*(F x/G x)*localGamma μ Q v v x) μ)
    (hie : Integrable (fun x => φ x*localGamma μ Q u v x) μ) :
    weightedGamma μ Q (fun x => φ x*(F x*G x)) (c • (V+a • U)) (c • (V+a • U)) =
      c^2*(a^2*(∫ x, φ x*(G x/F x)*localGamma μ Q u u x ∂μ)+
        (∫ x, φ x*(F x/G x)*localGamma μ Q v v x ∂μ)+2*a*weightedGamma μ Q φ u v) := by
  have he : (fun x => φ x*(F x*G x)*localGamma μ Q (c • (V+a • U)) (c • (V+a • U)) x)
      =ᵐ[μ] fun x => c^2*(a^2*(φ x*(G x/F x)*localGamma μ Q u u x)+
        φ x*(F x/G x)*localGamma μ Q v v x+2*a*(φ x*localGamma μ Q u v x)) := by
    filter_upwards [(ae_restrict_iff' hΩ).mp (local_logarithmic_grams μ Q F G u v U V hU hV),
      localGamma_linear_square μ Q U V a c] with x hg hl
    by_cases hx : x ∈ Ω
    · rw [hl,(hg hx).1,(hg hx).2.1,(hg hx).2.2]
      field_simp [(hF x hx).ne',(hG x hx).ne']
    · simp only [hs x hx,zero_mul,mul_zero,add_zero]
  have hs₁ := integral_add (hiu.const_mul (a^2)) hiv
  have hs₂ := integral_add ((hiu.const_mul (a^2)).add hiv) (hie.const_mul (2*a))
  simp only [Pi.add_apply] at hs₁ hs₂
  rw [weightedGamma,integral_congr_ae he,integral_const_mul,hs₂,hs₁,
    integral_const_mul,integral_const_mul]
  rfl

end RegularPointCoordinates

end

end OAI
