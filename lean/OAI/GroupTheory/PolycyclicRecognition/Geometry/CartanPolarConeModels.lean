import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredConeRealization

namespace OAI

/-! # Published inputs for the finite polar-cone models

This record only groups the already stated nilpotent existence, integration
and exponential Haar inputs. It contains no metric or profile conclusion.
It is instantiated separately for each ray or two-ray cone used below.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (C : Set (H →ₗ[ℝ] ℝ))

/-- The six published inputs actually used to realize a specified cone.
Lee's nilpotent existence/integration and Le Donne's exponential Haar
statements retain their original Lean propositions. -/
structure PolarConeModelInputs : Prop where
  existsQ : NilpotentLieExistenceInput ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)
  haarQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
    NilpotentExponentialHaarInput Q.modelSpace Q.carrier
  integratesQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
    NilpotentLieIntegrationInput (EN := F.N.modelSpace) (N := F.N.carrier)
      (EG := Q.modelSpace) (G := Q.carrier)
  existsI : NilpotentLieExistenceInput (M.coneWordIdeal C)
  haarI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
    NilpotentExponentialHaarInput I.modelSpace I.carrier
  integratesI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
    NilpotentLieIntegrationInput (EN := I.modelSpace) (N := I.carrier)
      (EG := F.N.modelSpace) (G := F.N.carrier)

variable [SimplyConnectedSpace G] {a : ℕ}
  (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (inputs : M.PolarConeModelInputs F C)

/-- Choose only the concrete measured cone required by the application. -/
def PolarConeModelInputs.model : M.MeasuredCone F C :=
  Classical.choice (M.nonempty_measuredCone_of_published_realization F C T hExp realize
    haarN inputs.existsQ inputs.haarQ inputs.integratesQ
    inputs.existsI inputs.haarI inputs.integratesI)

theorem PolarConeModelInputs.model_haarQ :
    NilpotentExponentialHaarInput
      (inputs.model M F C T hExp realize haarN).Q.modelSpace
      (inputs.model M F C T hExp realize haarN).Q.carrier :=
  inputs.haarQ _

theorem PolarConeModelInputs.model_haarI :
    NilpotentExponentialHaarInput
      (inputs.model M F C T hExp realize haarN).I.modelSpace
      (inputs.model M F C T hExp realize haarN).I.carrier :=
  inputs.haarI _

end PolycyclicRecognition.CartanWordModel

end

end OAI
