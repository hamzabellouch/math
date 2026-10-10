import Mathlib
import OAI.Analysis.WeakInfiniteness.ReducingColumns

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexOrder

variable {n : Type*} [Fintype n]

def scalarActionHom : CStarMatrix n n ℂ →⋆ₙₐ[ℂ]
    (HilbertVector n ℂ →L[ℂ] HilbertVector n ℂ) :=
  matrixRepresentation (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).toNonUnitalStarAlgHom n

lemma scalarActionHom_eq (D : CStarMatrix n n ℂ) :
    scalarActionHom D=scalarMatrixAction (H := ℂ) D := rfl

lemma scalarActionHom_injective : Function.Injective (scalarActionHom (n := n)) := by
  classical
  intro D E h
  ext i j
  have hh := congrArg (fun T : HilbertVector n ℂ →L[ℂ] HilbertVector n ℂ =>
    T (PiLp.single 2 j 1) i) h
  simpa [scalarActionHom_eq, scalarMatrixAction_apply, PiLp.single_apply, smul_eq_mul] using hh

lemma norm_scalarMatrixAction (D : CStarMatrix n n ℂ) :
    ‖scalarMatrixAction (H := ℂ) D‖=‖D‖ :=
  NonUnitalStarAlgHom.norm_map scalarActionHom scalarActionHom_injective D

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma exists_scalar_matrix_coordinates [FiniteDimensional ℂ H] (D : H →L[ℂ] H) :
    ∃ (d : ℕ) (e : H ≃ₗᵢ[ℂ] HilbertVector (Fin d) ℂ)
      (M : CStarMatrix (Fin d) (Fin d) ℂ),
      ‖M‖=‖D‖ ∧ scalarMatrixAction (H := ℂ) M=e.conjStarAlgEquiv D := by
  classical
  let b := stdOrthonormalBasis ℂ H
  let M : CStarMatrix (Fin (Module.finrank ℂ H)) (Fin (Module.finrank ℂ H)) ℂ :=
    fun i j => ⟪b i, D (b j)⟫_ℂ
  have he : scalarMatrixAction (H := ℂ) M=b.repr.conjStarAlgEquiv D := by
    ext x i
    obtain ⟨y,rfl⟩ := b.repr.surjective x
    rw [scalarMatrixAction_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    rw [b.repr.symm_apply_apply]
    simp only [M, OrthonormalBasis.repr_apply_apply, smul_eq_mul]
    conv_rhs => rw [← b.sum_repr' y]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  refine ⟨Module.finrank ℂ H,b.repr,M,?_,he⟩
  rw [← norm_scalarMatrixAction M, he]
  exact @StarAlgEquiv.norm_map _ (H →L[ℂ] H)
    (HilbertVector (Fin (Module.finrank ℂ H)) ℂ →L[ℂ] HilbertVector (Fin (Module.finrank ℂ H)) ℂ)
    _ _ _ _ _ b.repr.conjStarAlgEquiv D

end

end WeakPureInfiniteness
end

end OAI
