import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarConeModels
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinInput
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentCoordinatesInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIntegrationNaturality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentIntegrationConstruction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarConstruction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.DynkinGlobalExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnconditionalNilpotentModel

namespace OAI

/-! # The nilpotent published-input family used by the Cartan construction

The finite BCH expansion follows Baudoin (2004), Appendix B.5--B.6.
The intrinsic adjoint calculation and integration into arbitrary Lie groups
give model existence, global coordinates, integration, and exponential
Haar compatibility.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

structure NilpotentPublishedInputs : Prop where
  dynkin : ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L), NilpotentDynkinExpansionInput N.modelSpace N.carrier

/-- Codimension-one induction constructs the analytic simply connected model. -/
theorem NilpotentPublishedInputs.existsModel (_h : NilpotentPublishedInputs)
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L] :
    NilpotentLieExistenceInput L :=
  nilpotentLieExistenceInput L

/-- Finite BCH and simple connectedness give the global exponential chart. -/
theorem NilpotentPublishedInputs.coordinates (h : NilpotentPublishedInputs)
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) : NilpotentGlobalExponentialChartInput N.modelSpace N.carrier :=
  nilpotentGlobalExponentialChart_of_dynkin (h.dynkin L N)

/-- Global integral curves give the exponential, and the BCH Jacobian gives
the Haar compatibility of every exponential basis chart. -/
theorem NilpotentPublishedInputs.haar (h : NilpotentPublishedInputs)
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) : NilpotentExponentialHaarInput N.modelSpace N.carrier :=
  ((h.coordinates L N).toCoordinates (h.dynkin L N)).toHaar

/-- The nilpotent-target specialization is constructed from exponential
coordinates and the common BCH identity on the product group. -/
theorem NilpotentPublishedInputs.integrate (h : NilpotentPublishedInputs)
    (L K : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [LieRing K] [LieAlgebra ℝ K] [FiniteDimensional ℝ K] [LieRing.IsNilpotent K]
    (N : NilpotentLieModel L) (Q : NilpotentLieModel K) :
    NilpotentLieIntegrationInput (EN := N.modelSpace) (N := N.carrier)
      (EG := Q.modelSpace) (G := Q.carrier) :=
  nilpotentLieIntegrationInput_of_smooth
    (nilpotentSmoothIntegration_of_coordinates (h.coordinates L N) (h.coordinates K Q)
      h.dynkin (Q.tangent_nilpotent inferInstance))

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]

/-- The six inputs for each actual cone are specializations of the cited
nilpotent theorems. Cone geometry itself is not assumed. -/
theorem NilpotentPublishedInputs.polar (h : NilpotentPublishedInputs)
    (M : CartanWordModel H) {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G}
    (F : CartanFactorModel H Exp) (C : Set (H →ₗ[ℝ] ℝ)) :
    M.PolarConeModelInputs F C := by
  let : LieRing.IsNilpotent (cartanRootIdeal H) := LieModule.IsNilpotent.mk _ M.bound_zero
  let : LieRing.IsNilpotent ((cartanRootIdeal H) ⧸ M.coneWordIdeal C) :=
    (M.coneProjection_surjective C).lieAlgebra_isNilpotent
  exact {
    existsQ := h.existsModel _
    haarQ := h.haar _
    integratesQ := h.integrate _ _ F.N
    existsI := h.existsModel _
    haarI := h.haar _
    integratesI := fun I => h.integrate _ _ I F.N }

end PolycyclicRecognition

end

end OAI
