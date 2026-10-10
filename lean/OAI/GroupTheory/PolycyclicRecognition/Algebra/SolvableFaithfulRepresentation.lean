import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilshadowWeightAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FaithfulTruncatedEnveloping

namespace OAI

/-! # A faithful representation nilpotent on the canonical nilradical

The representation is obtained from the proved nilshadow and its finite
truncated enveloping algebra. Real triangularization is a separate step.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H

def solvableTruncatedRepresentation (c : ℕ) :
    L →ₗ⁅ℝ⁆ Module.End ℝ (TruncatedEnvelopingAlgebra ℝ K c) :=
  (truncatedSemidirectRepresentation c (nilshadowWeightAction T H).range.incl).comp
    (nilshadowSemidirectEmbedding T H)

theorem nilshadowWeightDerivation_eq_zero_of_mem_kernel (x : L) (hx : x ∈ T.kernelIdeal) :
    nilshadowWeightDerivation T H x = 0 := by
  have hσ : heightSemisimpleAction T H x = 0 := by
    change cartanWeightDerivationLinear T H
      (cartanHeightSection T H (heightProjection T.character x)) = 0
    have hz : heightProjection T.character x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [hz, map_zero, map_zero]
  apply LieDerivation.ext
  intro p
  apply (cartanNilshadowEquiv T H).symm.injective
  rw [nilshadowWeightDerivation_symm, hσ]
  simp

theorem solvableTruncatedRepresentation_nilpotent (c : ℕ) (x : L)
    (hx : x ∈ T.kernelIdeal) : IsNilpotent (solvableTruncatedRepresentation T H c x) := by
  change IsNilpotent (truncatedLeftRepresentation (R := ℝ) c (cartanNilshadowEquiv T H x) +
    truncatedEnvelopingDerivationRepresentation c (nilshadowWeightDerivation T H x))
  rw [nilshadowWeightDerivation_eq_zero_of_mem_kernel T H x hx, map_zero, add_zero]
  exact truncatedLeftRepresentation_nilpotent _ _

theorem solvableTruncatedRepresentation_injective (c : ℕ)
    (hgen : Function.Injective (truncatedEnvelopingGenerator (R := ℝ) (L := K) c)) :
    Function.Injective (solvableTruncatedRepresentation T H c) :=
  (truncatedSemidirectRepresentation_injective c _
    (show Function.Injective (nilshadowWeightAction T H).range.incl from
      Subtype.val_injective) hgen).comp
    (nilshadowSemidirectEmbedding_injective T H)

include H in
theorem exists_faithful_nilradical_matrix_representation :
    ∃ m : ℕ, ∃ j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      Function.Injective j ∧ ∀ x ∈ T.kernelIdeal, IsNilpotent (j x) := by
  let bK := finBasis ℝ K
  let : NormedAddCommGroup K := NormedAddCommGroup.induced K _ bK.equivFun bK.equivFun.injective
  let : NormedSpace ℝ K := NormedSpace.induced ℝ K _ bK.equivFun
  let : RealNormedLieAlgebra K :=
    { (inferInstance : NormedAddCommGroup K), (inferInstance : LieRing K),
      (inferInstance : NormedSpace ℝ K), (inferInstance : LieAlgebra ℝ K) with }
  obtain ⟨c, hfin, hgen⟩ := exists_faithful_truncated_enveloping K (cartanNilshadow_nilpotent T H)
  let := hfin
  let Q := TruncatedEnvelopingAlgebra ℝ K c
  let b := finBasis ℝ Q
  let ρ := solvableTruncatedRepresentation T H c
  let j := (LinearMap.toMatrixAlgEquiv b).toLieEquiv.toLieHom.comp ρ
  refine ⟨finrank ℝ Q, j, ?_, ?_⟩
  · exact (LinearMap.toMatrixAlgEquiv b).injective.comp
      (solvableTruncatedRepresentation_injective T H c hgen)
  · intro x hx
    exact (solvableTruncatedRepresentation_nilpotent T H c x hx).map
      (LinearMap.toMatrixAlgEquiv b).toRingHom

end PolycyclicRecognition

end

end OAI
