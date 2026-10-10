import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput

namespace OAI

/-! # The simply connected nilpotent Lie models needed by Cartan factorization

J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013),
Theorem 20.21, p.531, gives the simply connected integration of a finite
dimensional real Lie algebra. For the nilpotent case, exponential coordinates
have a finite polynomial BCH law: F. Baudoin, *An Introduction to the Geometry
of Stochastic Flows* (2004), Appendix B.5–B.6, pp.123–126. These coordinates
give the analytic Lie-group model used here. No metric-growth, Haar-volume,
Cartan-factorization, or quasi-isometry conclusion is included in this input.

The universe of the model can be chosen to match the algebra by using its
finite-dimensional coordinate space (or a lifted copy).
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

universe u

/-- Only the finite-dimensional simply connected integration data. Haar
measure and intrinsic exponentials are obtained from their separate input. -/
structure NilpotentLieModel (L : Type u) [LieRing L] [LieAlgebra ℝ L] where
  modelSpace : Type u
  [normedAddCommGroup : NormedAddCommGroup modelSpace]
  [normedSpace : NormedSpace ℝ modelSpace]
  [finiteDimensional : FiniteDimensional ℝ modelSpace]
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace modelSpace carrier]
  [group : Group carrier]
  [lieGroup : LieGroup (𝓘(ℝ, modelSpace)) ⊤ carrier]
  [t2Space : T2Space carrier]
  [simplyConnectedSpace : SimplyConnectedSpace carrier]
  [measurableSpace : MeasurableSpace carrier]
  [borelSpace : BorelSpace carrier]
  equiv : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, modelSpace)) carrier

attribute [instance] NilpotentLieModel.normedAddCommGroup NilpotentLieModel.normedSpace
  NilpotentLieModel.finiteDimensional NilpotentLieModel.topologicalSpace
  NilpotentLieModel.chartedSpace NilpotentLieModel.group NilpotentLieModel.lieGroup
  NilpotentLieModel.t2Space NilpotentLieModel.simplyConnectedSpace
  NilpotentLieModel.measurableSpace NilpotentLieModel.borelSpace

/-- The nilpotent specialization of Lie correspondence in exponential
polynomial coordinates. -/
def NilpotentLieExistenceInput (L : Type u) [LieRing L] [LieAlgebra ℝ L]
    [FiniteDimensional ℝ L] : Prop :=
  LieRing.IsNilpotent L → Nonempty (NilpotentLieModel L)

namespace NilpotentLieModel

variable {L : Type u} [LieRing L] [LieAlgebra ℝ L] (M : NilpotentLieModel L)

/-- Nilpotence is transported to the actual tangent algebra; it is not an
extra assumption about the chosen group. -/
theorem tangent_nilpotent (hnil : LieRing.IsNilpotent L) :
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, M.modelSpace)) M.carrier) :=
  M.equiv.nilpotent_iff_equiv_nilpotent.mp hnil

/-- The separate published exponential theorem supplies an actual chart
on the chosen model. -/
theorem exists_exponential_chart (hnil : LieRing.IsNilpotent L)
    (haar : NilpotentExponentialHaarInput M.modelSpace M.carrier) :
    ∃ Exp : GroupLieAlgebra (𝓘(ℝ, M.modelSpace)) M.carrier → M.carrier,
      IsGroupExponential Exp ∧
      ∃ chart : GroupLieAlgebra (𝓘(ℝ, M.modelSpace)) M.carrier ≃ₜ M.carrier,
        ∀ x, chart x = Exp x := by
  have hn := M.tangent_nilpotent hnil
  obtain ⟨Exp, hExp⟩ := haar.1 hn
  exact ⟨Exp, hExp, (haar.2 Exp hExp hn).1⟩

end NilpotentLieModel

end PolycyclicRecognition

end

end OAI
