import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem
import OAI.Analysis.KadisonSimilarity.Representation.OrthogonalColumns

namespace OAI

/-!
# Hilbert coordinates from a finite orthogonal family of corner inclusions

The two matrix-unit equations construct the coordinate unitaries used in the
full-column theorem. The action of an arbitrary operator is then its actual
matrix of corner compressions.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMap

variable {F H : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The elementary operator equations supplied by a complete finite system of
matrix-unit columns. -/
structure FiniteOrthogonalColumns (F H : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) where
  inclusion : Fin n → F →L[ℂ] H
  adjoint_comp : ∀ i j, (inclusion i).adjoint.comp (inclusion j) =
    if i = j then ContinuousLinearMap.id ℂ F else 0
  resolution : ∑ i, (inclusion i).comp (inclusion i).adjoint = ContinuousLinearMap.id ℂ H

namespace FiniteOrthogonalColumns

variable {n : ℕ} (U : FiniteOrthogonalColumns F H n)

@[simp] theorem adjoint_inclusion_apply (i j : Fin n) (x : F) :
    (U.inclusion i).adjoint (U.inclusion j x) = if i = j then x else 0 := by
  have h := congrArg (fun T : F →L[ℂ] F => T x) (U.adjoint_comp i j)
  by_cases hij : i = j
  · simpa [hij] using h
  · simpa [hij] using h

/-- Orthogonality makes assembly an isometry. -/
theorem adjoint_assembly_comp_assembly :
    (sumColumns U.inclusion).adjoint.comp (sumColumns U.inclusion) =
      ContinuousLinearMap.id ℂ (HilbertCopies F n) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  change ((sumColumns U.inclusion).adjoint (sumColumns U.inclusion x)) i = x i
  rw [sumColumns_adjoint_apply, sumColumns_apply, map_sum]
  simp only [U.adjoint_inclusion_apply]
  simp

/-- Completeness of the family makes assembly onto the full Hilbert space. -/
theorem assembly_comp_adjoint_assembly :
    (sumColumns U.inclusion).comp (sumColumns U.inclusion).adjoint =
      ContinuousLinearMap.id ℂ H := by
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => T x) U.resolution
  simpa only [comp_apply, sum_apply, id_apply, sumColumns_apply,
    sumColumns_adjoint_apply] using h

/-- The coordinate unitary is constructed from the finite matrix-unit columns. -/
def unitary : HilbertCopies F n ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofLinearIsometry
    { toLinearMap := (sumColumns U.inclusion).toLinearMap
      norm_map' := (norm_map_iff_adjoint_comp_self _).mpr U.adjoint_assembly_comp_assembly }
    (sumColumns U.inclusion).adjoint.toLinearMap
    (congrArg ContinuousLinearMap.toLinearMap U.assembly_comp_adjoint_assembly)
    (congrArg ContinuousLinearMap.toLinearMap U.adjoint_assembly_comp_assembly)

@[simp] theorem unitary_apply (x : HilbertCopies F n) :
    U.unitary x = sumColumns U.inclusion x := rfl

@[simp] theorem unitary_symm_apply (x : H) :
    U.unitary.symm x = (sumColumns U.inclusion).adjoint x := rfl

@[simp] theorem unitary_single (i : Fin n) (x : F) :
    U.unitary (PiLp.single 2 i x) = U.inclusion i x := by
  simp only [unitary_apply, sumColumns_apply, PiLp.single_apply, apply_ite, map_zero]
  simp

/-- Arbitrary operators act in the constructed coordinates by their corner
compression matrix. -/
theorem coordinates_operator (T : H →L[ℂ] H) (x : H) :
    U.unitary.symm (T x) =
      matrixOperator (fun i j => (U.inclusion i).adjoint.comp (T.comp (U.inclusion j)))
        (U.unitary.symm x) := by
  rw [← sumColumns_compression]
  change (sumColumns U.inclusion).adjoint (T x) =
    (sumColumns U.inclusion).adjoint (T (U.unitary (U.unitary.symm x)))
  rw [U.unitary.apply_symm_apply]

/-- A coordinate matrix unit is the actual matrix unit formed from the two
corner inclusions. -/
theorem unitary_matrixUnit (i j : Fin n) (x : H) :
    U.unitary (copyMatrixUnit i j (U.unitary.symm x)) =
      U.inclusion i ((U.inclusion j).adjoint x) := by
  simp only [unitary_apply, copyMatrixUnit_apply, unitary_symm_apply,
    sumColumns_adjoint_apply, sumColumns_apply, PiLp.single_apply, apply_ite, map_zero]
  simp

end FiniteOrthogonalColumns

section Representations

variable {P C D K : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Realize the full-column coordinates from the actual corner inclusion
operators and their common matrix of algebra entries. -/
def fullColumnCoordinatesOfColumns
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (U : FiniteOrthogonalColumns F H n) (V : FiniteOrthogonalColumns K D n)
    (entry : P → Matrix (Fin n) (Fin n) C)
    (hU : ∀ a i j, ρ (entry a i j) =
      (U.inclusion i).adjoint.comp ((L a).comp (U.inclusion j)))
    (hV : ∀ a i j, σ (entry a i j) =
      (V.inclusion i).adjoint.comp ((Lr a).comp (V.inclusion j))) :
    FullColumnCoordinates L Lr ρ σ n where
  domain := V.unitary.symm
  codomain := U.unitary.symm
  entry := entry
  domain_action := by
    intro a x
    simpa only [hV] using V.coordinates_operator (Lr a) x
  codomain_action := by
    intro a x
    simpa only [hU] using U.coordinates_operator (L a) x

/-- The corner used by the full-column theorem is the concrete rectangular
compression of the given operator. -/
theorem fullColumnCoordinatesOfColumns_corner
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (U : FiniteOrthogonalColumns F H n) (V : FiniteOrthogonalColumns K D n)
    (entry : P → Matrix (Fin n) (Fin n) C)
    (hU : ∀ a i j, ρ (entry a i j) =
      (U.inclusion i).adjoint.comp ((L a).comp (U.inclusion j)))
    (hV : ∀ a i j, σ (entry a i j) =
      (V.inclusion i).adjoint.comp ((Lr a).comp (V.inclusion j)))
    (G : D →L[ℂ] H) (i : Fin n) :
    (fullColumnCoordinatesOfColumns L Lr ρ σ U V entry hU hV).corner i G =
      (U.inclusion i).adjoint.comp (G.comp (V.inclusion i)) := by
  ext x
  change (U.unitary.symm (G (V.unitary (PiLp.single 2 i x)))) i =
    (U.inclusion i).adjoint (G (V.inclusion i x))
  rw [V.unitary_single, U.unitary_symm_apply, sumColumns_adjoint_apply]

/-- Intertwining the actual matrix units becomes the scalar matrix-unit
commutation required by the full-column theorem. -/
theorem matrixUnit_intertwining_in_coordinates
    {n : ℕ} (U : FiniteOrthogonalColumns F H n) (V : FiniteOrthogonalColumns K D n)
    (G : D →L[ℂ] H) (i : Fin n)
    (hG : ∀ j : Fin n,
      G.comp ((V.inclusion i).comp (V.inclusion j).adjoint) =
        ((U.inclusion i).comp (U.inclusion j).adjoint).comp G) :
    ∀ j : Fin n,
      (U.unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (G.comp V.unitary.toContinuousLinearEquiv.toContinuousLinearMap)).comp
          (copyMatrixUnit i j) =
      (copyMatrixUnit i j).comp
        (U.unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (G.comp V.unitary.toContinuousLinearEquiv.toContinuousLinearMap)) := by
  intro j
  apply ContinuousLinearMap.ext
  intro x
  apply U.unitary.injective
  simp only [comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, U.unitary.apply_symm_apply]
  have hleft : V.unitary (copyMatrixUnit i j x) =
      V.inclusion i ((V.inclusion j).adjoint (V.unitary x)) := by
    simpa only [V.unitary.symm_apply_apply] using V.unitary_matrixUnit i j (V.unitary x)
  rw [hleft, U.unitary_matrixUnit]
  have h := congrArg (fun T : D →L[ℂ] H => T (V.unitary x)) (hG j)
  simpa only [comp_apply] using h

end Representations
end KadisonSimilarity

end

end OAI
