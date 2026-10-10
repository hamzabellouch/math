import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileParameterContinuity

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

/-- A Cartan chart, in the coordinates used for the profiles. -/
def CartanFactorModel.profileChart
    (bD : Basis (Fin (finrank ℝ H)) ℝ H) : (Fin (finrank ℝ H) → ℝ) → G :=
  fun z => F.inclusionD (F.ExpD (F.D.equiv (bD.equivFun.symm z)))

omit [IsTopologicalGroup G] in
theorem CartanFactorModel.continuous_profileChart
    (hD : Continuous F.ExpD) (bD : Basis (Fin (finrank ℝ H)) ℝ H) :
    Continuous (F.profileChart bD) :=
  F.closedD.continuous.comp (hD.comp
    (F.D.equiv.toLinearMap.comp bD.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)

/-- The original sample is multiplied by the actual probe prefix. -/
def CartanFactorModel.sampledProbeSuffix
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (v : cartanRootIdeal H) : G :=
  F.inclusionN (F.ExpN (F.N.equiv (bN.equivFun.symm y)) *
    F.ExpN (F.N.equiv v))

/-- This is a continuous map on the whole Cartan chart, before restricting
to the compact set chosen for all three paths. -/
def CartanFactorModel.sampledProbeProfile
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H)
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (v : cartanRootIdeal H) :
    C((Fin (finrank ℝ H) → ℝ), W) :=
  rescaledContinuousProfile J hJ x (F.sampledProbeSuffix bN y v) r
    (F.profileChart bD) (F.continuous_profileChart hD bD)

@[simp] theorem CartanFactorModel.sampledProbeProfile_apply
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H)
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (v : cartanRootIdeal H)
    (z : Fin (finrank ℝ H) → ℝ) :
    F.sampledProbeProfile hD J hJ x r bN bD y v z =
      rescaledMapProfile J x
        (F.inclusionN (F.ExpN (F.N.equiv (bN.equivFun.symm y))) *
          F.inclusionN (F.ExpN (F.N.equiv v))) r
        (fun z => F.inclusionD (F.ExpD (F.D.equiv (bD.equivFun.symm z)))) z := by
  simp only [sampledProbeProfile, sampledProbeSuffix, map_mul]
  rfl

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

/-- A Borel logarithmic prefix, including a tile-selected anchor, gives a
Borel actual profile under the independent product sampling law. -/
theorem CartanFactorModel.measurable_sampledProbeProfile
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (b₀ bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H)
    {Y : Type*} [MeasurableSpace Y] (v : Y → cartanRootIdeal H)
    (hv : Measurable (fun y => b₀.equivFun (v y))) :
    Measurable (fun p : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × Y =>
      F.sampledProbeProfile hD J hJ x r bN bD p.1 (v p.2)) := by
  let Ncoords : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → G :=
    fun z => F.inclusionN (F.ExpN (F.N.equiv (b₀.equivFun.symm z)))
  have hNc : Continuous Ncoords :=
    F.closedN.continuous.comp (hN.comp
      (F.N.equiv.toLinearMap.comp b₀.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)
  have hNv : Measurable (fun y => F.inclusionN (F.ExpN (F.N.equiv (v y)))) := by
    have hm := hNc.measurable.comp hv
    change Measurable (fun y => F.inclusionN
      (F.ExpN (F.N.equiv (b₀.equivFun.symm (b₀.equivFun (v y)))))) at hm
    simpa only [LinearEquiv.symm_apply_apply] using hm
  have hsample : Continuous (fun y => F.inclusionN (F.ExpN (F.N.equiv (bN.equivFun.symm y)))) :=
    F.closedN.continuous.comp (hN.comp
      (F.N.equiv.toLinearMap.comp bN.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)
  simpa only [sampledProbeProfile, sampledProbeSuffix, map_mul, Function.comp_def, Pi.mul_apply] using
    (continuous_rescaledContinuousProfile J hJ x r
    (F.profileChart bD) (F.continuous_profileChart hD bD)).measurable.comp
      ((hsample.measurable.comp measurable_fst).mul (hNv.comp measurable_snd))

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
    [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)] in
/-- The initial and final profiles agree exactly when the actual group
suffixes agree. In particular this identifies the third chain's initial
profile with the second chain's terminal anchor. -/
theorem CartanFactorModel.sampledProbeProfile_eq_of_exp_eq
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H)
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (u v : cartanRootIdeal H)
    (h : F.ExpN (F.N.equiv u) = F.ExpN (F.N.equiv v)) :
    F.sampledProbeProfile hD J hJ x r bN bD y u =
      F.sampledProbeProfile hD J hJ x r bN bD y v := by
  unfold sampledProbeProfile sampledProbeSuffix
  rw [h]

end PolycyclicRecognition

end

end OAI
