import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualProbeProfiles

namespace OAI

/-! # The original center and exact group frames of a sampled profile -/

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

/-- The root element selected by the independent coordinate-cube sample. -/
def CartanFactorModel.sampleRoot
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) : F.N.carrier :=
  F.ExpN (F.N.equiv (bN.equivFun.symm y))

omit [IsTopologicalGroup G] in
/-- An endpoint identity can be used without changing the profile center. -/
theorem CartanFactorModel.sampledProbeSuffix_eq
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (v : cartanRootIdeal H)
    (u : F.N.carrier) (hu : F.ExpN (F.N.equiv v) = u) :
    F.sampledProbeSuffix bN y v = F.inclusionN (F.sampleRoot bN y * u) := by
  simp only [sampledProbeSuffix, sampleRoot, map_mul, hu]

omit [IsTopologicalGroup G] in
/-- The endpoint in exponential coordinates and its group-valued frame agree. -/
theorem CartanFactorModel.sampledProbeSuffix_eq_root
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (v : cartanRootIdeal H) :
    F.sampledProbeSuffix bN y v =
      F.inclusionN (F.sampleRoot bN y * F.ExpN (F.N.equiv v)) :=
  F.sampledProbeSuffix_eq bN y v _ rfl

/-- Restricting the chart does not re-center a sampled profile. This is the
identity needed by the source count, including the original subtracted value. -/
theorem CartanFactorModel.sampledProbeProfile_eq
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H)
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (v : cartanRootIdeal H)
    (u : F.N.carrier) (hu : F.ExpN (F.N.equiv v) = u)
    {Z : Set (Fin (finrank ℝ H) → ℝ)} (z : Z) :
    F.sampledProbeProfile hD J hJ x r bN bD y v z =
      rescaledMapProfile J x (F.inclusionN (F.sampleRoot bN y * u)) r
        (fun z : Z => F.profileChart bD z.val) z := by
  change rescaledMapProfile J x (F.sampledProbeSuffix bN y v) r
    (F.profileChart bD) z.val = _
  rw [F.sampledProbeSuffix_eq bN y v u hu]
  rfl

omit [IsTopologicalGroup G] in
/-- The chart point corresponding to a physical Cartan vector is exact even
when the logarithmic rescaling basis moves with the scale. -/
theorem CartanFactorModel.profileChart_coordinates
    (bD : Basis (Fin (finrank ℝ H)) ℝ H) (v : H) :
    F.profileChart bD (bD.equivFun v) = F.inclusionD (F.ExpD (F.D.equiv v)) := by
  simp only [profileChart, LinearEquiv.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
