import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # Two-direction polarization of actual Sobolev Gram representatives -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem sobolev_gram_polarization (u v A B S : SobolevSpace μ Q)
    (hA : SobolevSpace.toLp μ Q A =ᵐ[μ] localGamma μ Q u u)
    (hB : SobolevSpace.toLp μ Q B =ᵐ[μ] localGamma μ Q v v)
    (hS : SobolevSpace.toLp μ Q S =ᵐ[μ] localGamma μ Q (u+v) (u+v)) :
    SobolevSpace.toLp μ Q ((1/2:ℝ) • (S-A-B)) =ᵐ[μ] localGamma μ Q u v := by
  rw [map_smul,map_sub,map_sub]
  filter_upwards [hA,hB,hS,
    Lp.coeFn_sub (SobolevSpace.toLp μ Q S) (SobolevSpace.toLp μ Q A),
    Lp.coeFn_sub (SobolevSpace.toLp μ Q S-SobolevSpace.toLp μ Q A) (SobolevSpace.toLp μ Q B),
    Lp.coeFn_smul (1/2:ℝ) (SobolevSpace.toLp μ Q S-SobolevSpace.toLp μ Q A-SobolevSpace.toLp μ Q B),
    localGamma_add_left μ Q u v (u+v),localGamma_add_right μ Q u u v,
    localGamma_add_right μ Q v u v,localGamma_comm μ Q v u]
      with x ha hb hs hab hsab hc hadd hu hv hsym
  dsimp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hab hsab hc hadd hu hv
  rw [hc,hsab,hab,ha,hb,hs,hadd,hu,hv,hsym]
  ring

end RegularPointCoordinates

end

end OAI
