import OAI.Geometry.RCD.Heat.LocalLogarithmGammaByValue

namespace OAI

/-! # The logarithmic-density flux retains the full cutoff-gradient term -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem local_logarithmic_sum_flux {Ω : Set X} (hΩ : MeasurableSet Ω)
    (F G : X → ℝ) (hF : ∀ x ∈ Ω, 0 < F x) (hG : ∀ x ∈ Ω, 0 < G x)
    (u v U V w : SobolevSpace μ Q) (c : ℝ)
    (hU : localGamma μ Q U w =ᵐ[μ.restrict Ω] fun x => localGamma μ Q u w x/F x)
    (hV : localGamma μ Q V w =ᵐ[μ.restrict Ω] fun x => localGamma μ Q v w x/G x)
    (hw : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q w x=0) :
    (fun x => c*(G x*localGamma μ Q u w x+F x*localGamma μ Q v w x)) =ᵐ[μ]
      fun x => F x*G x*localGamma μ Q (c • (U+V)) w x := by
  filter_upwards [(ae_restrict_iff' hΩ).mp hU,(ae_restrict_iff' hΩ).mp hV,hw,
    localGamma_smul_left μ Q c (U+V) w,localGamma_add_left μ Q U V w,
    localGamma_zero_on_level μ Q w u 0,localGamma_zero_on_level μ Q w v 0,
    localGamma_zero_on_level μ Q w (c • (U+V)) 0,
    localGamma_comm μ Q u w,localGamma_comm μ Q v w,localGamma_comm μ Q (c • (U+V)) w]
    with x hUx hVx hwx hc ha hzu hzv hzS hcu hcv hcS
  by_cases hx : x ∈ Ω
  · rw [hc,ha,hUx hx,hVx hx]
    field_simp [(hF x hx).ne',(hG x hx).ne']
  · have hz := hwx hx
    rw [hcu,hcv,hcS,hzu hz,hzv hz,hzS hz]
    ring

end RegularPointCoordinates

end

end OAI
