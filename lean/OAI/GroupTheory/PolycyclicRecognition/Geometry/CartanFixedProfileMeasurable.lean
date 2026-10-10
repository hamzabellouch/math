import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualProbeProfiles

namespace OAI

/-! # The actual measurable profiles of the sampled probe chains -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

/-- The fixed initial suffix is a continuous function of the original sample.
This proof avoids introducing an artificial product probe space. -/
theorem CartanFactorModel.measurable_fixed_sampledProbeProfile
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H) (v : cartanRootIdeal H)
    (Z : Set (Fin (finrank ℝ H) → ℝ))
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)] :
    Measurable (fun y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ =>
      (F.sampledProbeProfile hD J hJ x r bN bD y v).restrict Z) := by
  have hs : Continuous (fun y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ =>
      F.sampledProbeSuffix bN y v) := by
    simpa only [CartanFactorModel.sampledProbeSuffix, map_mul, Function.comp_apply,
      LinearMap.comp_apply, LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, LinearEquiv.coe_coe] using
      (F.closedN.continuous.comp (hN.comp
      (F.N.equiv.toLinearMap.comp bN.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)).mul_const _
  exact ((ContinuousMap.continuous_restrict Z).comp
    ((continuous_rescaledContinuousProfile J hJ x r
      (F.profileChart bD) (F.continuous_profileChart hD bD)).comp hs)).measurable

end PolycyclicRecognition

end

end OAI
