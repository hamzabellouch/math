import OAI.Geometry.RCD.Heat.LocalLogarithmicGradient
import OAI.Geometry.RCD.Sobolev.HessianActionLocality

namespace OAI

/-! # The logarithmic Gamma rule for any local Sobolev representative -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem local_logarithm_gamma_of_value {Ω : Set X}
    (u U : SobolevSpace μ Q) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ Q u x ∈ Icc a b)
    (hU : SobolevSpace.toLp μ Q U =ᵐ[μ.restrict Ω]
      fun x => Real.log (SobolevSpace.toLp μ Q u x))
    (w : SobolevSpace μ Q) :
    localGamma μ Q U w =ᵐ[μ.restrict Ω]
      fun x => localGamma μ Q u w x/SobolevSpace.toLp μ Q u x := by
  obtain ⟨φ,ψ,χ,C,D,B,E,hφ,hψ,-,hφ0,-,hdφ,-,hB,-,he⟩ :=
    exists_local_smooth_log ha hab
  let V := SobolevSpace.comp μ Q hφ hφ0 u
  have hsame : SobolevSpace.toLp μ Q V =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q U := by
    filter_upwards [ae_restrict_of_ae (SobolevSpace.comp_coe μ Q hφ hφ0 u),hu,hU]
      with x hx hy hz
    exact (hx.trans (he _ hy).1).trans hz.symm
  filter_upwards [localGamma_pair_congr_ae μ Q hsame (EventuallyEq.refl _ w.val),
    ae_restrict_of_ae (localGamma_comp_C1 μ Q u w hφ hφ0 hψ.continuous hdφ B hB),hu]
    with x hx hy hz
  rw [← hx,hy,(he _ hz).2.1,div_eq_mul_inv,mul_comm]

end RegularPointCoordinates

end

end OAI
