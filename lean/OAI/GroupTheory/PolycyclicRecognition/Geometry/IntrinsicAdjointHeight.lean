import OAI.GroupTheory.PolycyclicRecognition.Geometry.AdjointMatrixHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBasisGeneration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointExponential

namespace OAI

/-! # Intrinsic adjoint height on a connected triangular Lie group

The actual adjoint action is positive upper triangular because this holds
on exponential basis curves, which generate the connected group. Its
logarithmic diagonal is therefore a continuous character without a global
exponential chart or a faithful group representation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem adjointMatrixHom_exp_intrinsic {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    adjointMatrixHom b (Exp x) =
      NormedSpace.exp (LinearMap.toMatrix b b (LieAlgebra.ad ℝ _ x)) := by
  let f : (E →L[ℝ] E) →+* Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrixAlgEquiv b).toRingHom.comp ContinuousLinearMap.toLinearMapRingHom
  let fL : (E →L[ℝ] E) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have he := adjointLinearMap_exponential hExp x 1
  simp only [one_smul] at he
  have hm := NormedSpace.map_exp f fL.continuous_of_finiteDimensional
    (groupAdjointOperator (E := E) x)
  change f (adjointLinearMap (E := E) (Exp x)) = _
  rw [he]
  exact hm

theorem continuous_adjointMatrixHom {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    Continuous (adjointMatrixHom b : G → Matrix (Fin n) (Fin n) ℝ) := by
  let fL : (E →L[ℝ] E) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  change Continuous (fun g => fL (conjugationDifferentialHom (E := E) g))
  exact fL.continuous_of_finiteDimensional.comp contMDiff_conjugationDifferentialHom.continuous

variable [IsTopologicalGroup G] [PreconnectedSpace G]

theorem adjointMatrixHom_positive_triangular {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (g : G) : (adjointMatrixHom T.basis g).IsUpperTriangular ∧
      ∀ i, 0 < adjointMatrixHom T.basis g i i := by
  let ρ := (adjointMatrixHom T.basis).toHomUnits
  let S := (positiveTriangular n).comap ρ
  have hS : S = ⊤ := by
    apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
    intro i t
    change (adjointMatrixHom T.basis (Exp (t • Module.finBasis ℝ E i))).IsUpperTriangular ∧
      ∀ j, 0 < adjointMatrixHom T.basis (Exp (t • Module.finBasis ℝ E i)) j j
    have he := adjointMatrixHom_exp_intrinsic T.basis hExp (t • Module.finBasis ℝ E i)
    constructor
    · exact he.symm ▸ matrix_exp_upperTriangular _ (T.upper _)
    · intro j
      have hp : 0 < NormedSpace.exp
          (LinearMap.toMatrix T.basis T.basis (LieAlgebra.ad ℝ _
            (t • Module.finBasis ℝ E i))) j j := by
        exact (matrix_exp_diagonal _ (T.upper _) j).symm ▸ Real.exp_pos _
      exact he.symm ▸ hp
  have hg : g ∈ S := by rw [hS]; trivial
  exact hg

/-- The character is constructed from the actual adjoint action. -/
def intrinsicAdjointCharacterHom {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    G →* Multiplicative (Fin n → ℝ) :=
  matrixLogDiagonalHom (adjointMatrixHom T.basis)
    (fun g => (adjointMatrixHom_positive_triangular T hExp g).1)
    (fun g => (adjointMatrixHom_positive_triangular T hExp g).2)

theorem intrinsicAdjointCharacterHom_exp {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) (i : Fin n) :
    (intrinsicAdjointCharacterHom T hExp (Exp x)).toAdd i = T.character i x := by
  change Real.log (adjointMatrixHom T.basis (Exp x) i i) = _
  rw [adjointMatrixHom_exp_intrinsic T.basis hExp,
    matrix_exp_diagonal _ (T.upper x), Real.log_exp, T.character_eq_diag]

theorem continuous_intrinsicAdjointCharacterHom {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    Continuous (fun g => (intrinsicAdjointCharacterHom T hExp g).toAdd) := by
  apply continuous_pi
  intro i
  change Continuous (fun g => Real.log (adjointMatrixHom T.basis g i i))
  exact ((continuous_apply i).comp
    ((continuous_apply i).comp (continuous_adjointMatrixHom T.basis))).log
    (fun g => ((adjointMatrixHom_positive_triangular T hExp g).2 i).ne')

end PolycyclicRecognition

end

end OAI
