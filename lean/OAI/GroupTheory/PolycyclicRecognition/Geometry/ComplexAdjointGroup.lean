import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexAdjointKernel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexMatrixExtension
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexWeightLift

namespace OAI

/-! # Additive complex adjoint weights on a simply connected solvable group -/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped Manifold TensorProduct Matrix.Norms.Operator

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [IsTopologicalGroup G] [PreconnectedSpace G] {m n : ℕ}

/-- The triangular infinitesimal adjoint action exponentiates to a
triangular group action, using only local exponential generation. -/
theorem complexAdjointMatrixHom_upper
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (g : G) : (complexAdjointMatrixHom b T.basis g).IsUpperTriangular := by
  let ρ := complexAdjointMatrixHom b T.basis
  let S : Subgroup G :=
    { carrier := {g | (ρ g).IsUpperTriangular ∧ (ρ (g⁻¹)).IsUpperTriangular}
      one_mem' := by
        have hone : (1 : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular := by
          intro i j hji
          change j < i at hji
          simp only [Matrix.one_apply, ite_eq_right_iff]
          intro hij
          exact False.elim ((ne_of_gt hji) hij)
        change (ρ 1).IsUpperTriangular ∧ (ρ ((1 : G)⁻¹)).IsUpperTriangular
        simpa only [inv_one, map_one] using And.intro hone hone
      mul_mem' := by
        intro a b ha hb
        exact ⟨by simpa only [map_mul] using ha.1.mul hb.1,
          by simpa only [mul_inv_rev, map_mul] using hb.2.mul ha.2⟩
      inv_mem' := by intro g hg; exact ⟨hg.2, by simpa using hg.1⟩ }
  have he (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
      (ρ (Exp x)).IsUpperTriangular := by
    rw [complexAdjointMatrixHom_exp b T.basis hExp]
    exact complex_matrix_exp_upperTriangular _ (T.upper _)
  have hinv (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
      (ρ ((Exp x)⁻¹)).IsUpperTriangular :=
    (congrArg (fun g : G => (ρ g).IsUpperTriangular) (hExp.map_neg x)).mp (he (-x))
  have hS : S = ⊤ := by
    apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
    intro i t
    constructor
    · exact he _
    · exact hinv _
  have hg : g ∈ S := by rw [hS]; trivial
  exact hg.1

theorem exists_additive_complex_adjoint_weights
    [SimplyConnectedSpace G] [LocallyPathConnectedSpace G]
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    ∃ π : G →* Multiplicative (Fin n → ℂ), Continuous (fun g => (π g).toAdd) ∧
      ∀ x, (π (Exp x)).toAdd = T.weightMap x := by
  apply exists_lifted_complex_matrix_weights (complexAdjointMatrixHom b T.basis)
    (continuous_complexAdjointMatrixHom b T.basis)
    (complexAdjointMatrixHom_upper b T hExp) T.weightMap Exp hExp.map_zero
    (fun x => (hExp.contMDiff_curve x).continuous)
  intro x i
  rw [complexAdjointMatrixHom_exp b T.basis hExp]
  simp only [complexifiedAdjointMatrix_apply]
  rw [complex_matrix_exp_diagonal _ (T.upper _)]
  rfl

end PolycyclicRecognition

end

end OAI
