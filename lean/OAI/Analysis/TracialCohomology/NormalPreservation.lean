import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.HilbertNormalParts
import OAI.Analysis.TracialCohomology.DominatedFactorization
import OAI.Analysis.TracialCohomology.BidualApproximation

namespace OAI

/-! Normal preservation for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem scalar_bilinear_normal_preservation (B : M →L[ℂ] StrongDual ℂ M)
    (hn : ∀ b, B.flip b ∈ normalDual e) (b : M) :
    ((scalarNormalPart e).comp B).flip b ∈ normalDual e := by
  obtain ⟨H,hH,hI,hcomp,β,C,hC,hdom⟩ :=
    HochschildDomination.exists_quartic_hilbert_modulus B
  let := hH
  let := hI
  let := hcomp
  let z : StrongDual ℂ (StrongDual ℂ M) :=
    ((ContinuousLinearMap.apply ℂ ℂ) b).comp (scalarNormalPart e)
  let w : H := hilbertNormalPart e β b
  have hw (φ : StrongDual ℂ H) : φ w = z (φ.comp β) :=
    hilbertNormalPart_pairing e β b φ
  obtain ⟨y,hy,he⟩ := HochschildApproximation.closed_subspace_preserved_of_quartic
    B.flip β hC hdom (normalDual e) (normalDual_closed e) hn z w hw
  have hN : ((scalarNormalPart e).comp B).flip b = y := by
    ext a
    exact (he ((ContinuousLinearMap.apply ℂ ℂ) a)).symm
  rw [hN]
  exact hy

open BoundedHochschild in

theorem operator_bilinear_normal_preservation (B : M →L[ℂ] M →L[ℂ] M)
    (hn : ∀ b, HasPreadjoint e (B.flip b)) (b : M) :
    HasPreadjoint e (((operatorNormalPart e).comp B).flip b) := by
  rw [hasPreadjoint_iff_scalar]
  intro z
  let Bz : M →L[ℂ] StrongDual ℂ M :=
    (ContinuousLinearMap.compL ℂ M M ℂ (predualEmbedding e z)).comp B
  have hzn (c : M) : Bz.flip c ∈ normalDual e :=
    (hasPreadjoint_iff_scalar e (B.flip c)).mp (hn c) z
  have h := scalar_bilinear_normal_preservation e Bz hzn b
  have heq : (predualEmbedding e z).comp (((operatorNormalPart e).comp B).flip b) =
      ((scalarNormalPart e).comp Bz).flip b := by
    ext a
    exact operatorNormalPart_pairing e (B a) b z
  rw [heq]
  exact h

end HochschildNormalPart

namespace BoundedHochschild
universe u v
variable {M : Type u} {X : Type v} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in
omit [CompleteSpace X] in
theorem predual_small : Small.{u} X := by
  apply small_of_injective (f := fun z : X => fun a : M => e.symm a z)
  intro x y h
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  simpa only [e.symm_apply_apply] using congrFun h (e φ)

def dualIsometry {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : Y ≃ₗᵢ[ℂ] X) : StrongDual ℂ Y ≃ₗᵢ[ℂ] StrongDual ℂ X where
  toFun φ := φ.comp T.symm.toContinuousLinearEquiv.toContinuousLinearMap
  invFun ψ := ψ.comp T.toContinuousLinearEquiv.toContinuousLinearMap
  left_inv φ := by ext y; simp
  right_inv ψ := by ext x; simp
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl
  norm_map' φ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      change ‖φ (T.symm x)‖ ≤ ‖φ‖ * ‖x‖
      simpa only [T.symm.norm_map] using φ.le_opNorm (T.symm x)
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro y
      have h := (φ.comp T.symm.toContinuousLinearEquiv.toContinuousLinearMap).le_opNorm (T y)
      simpa using h

include e in
theorem exists_same_universe_predual :
    ∃ (Y : Type u) (_ : NormedAddCommGroup Y) (_ : NormedSpace ℂ Y)
      (_ : CompleteSpace Y), Nonempty (Y ≃ₗᵢ[ℂ] X) := by
  let := predual_small e
  let Y := Shrink.{u} X
  let E : Y ≃ X := (equivShrink X).symm
  let : NormedAddCommGroup Y := E.normedAddCommGroup
  let : NormedSpace ℂ Y := E.addEquiv.normedSpace ℂ
  let T : Y ≃ₗᵢ[ℂ] X := { E.addEquiv.linearEquiv ℂ with norm_map' := fun _ => rfl }
  let : CompleteSpace Y := T.toIsometryEquiv.completeSpace_iff.mpr inferInstance
  exact ⟨Y,inferInstance,inferInstance,inferInstance,⟨T⟩⟩

end BoundedHochschild

end

end OAI
