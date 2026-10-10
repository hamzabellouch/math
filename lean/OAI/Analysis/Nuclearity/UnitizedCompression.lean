import OAI.Analysis.PureInfiniteness.SpectralMaps
import OAI.Analysis.PureInfiniteness.FiniteSpectralCompression

namespace OAI

/-! The finite row compression stays in the original nonunital algebra. Its
unitized matrix image is used only to apply the scalar sampling estimates. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A J : Type*} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A] [Fintype J]

def unitizationOneByOne : A →⋆ₙₐ[ℂ] CStarMatrix (Fin 1) (Fin 1) (Unitization ℂ A) :=
  (CStarMatrix.toOneByOne (Fin 1) ℂ (Unitization ℂ A)).toNonUnitalStarAlgHom.comp
    (Unitization.inrNonUnitalStarAlgHom ℂ A)

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizationOneByOne_injective : Function.Injective (unitizationOneByOne (A := A)) :=
  (CStarMatrix.toOneByOne (Fin 1) ℂ (Unitization ℂ A)).injective.comp
    (Unitization.inr_injective (R := ℂ))

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizationOneByOne_norm (a : A) : ‖unitizationOneByOne a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map unitizationOneByOne unitizationOneByOne_injective a

def finiteRowCompression (H : CStarMatrix (Fin 1) J A) (g : J → A) : A :=
  ∑ j, H 0 j * CFC.sqrt (g j)

lemma unitizationOneByOne_rowCompression (H : CStarMatrix (Fin 1) J A) (g : J → A)
    (hg : ∀ j, 0 ≤ g j) :
    unitizationOneByOne (finiteRowCompression H g) =
      rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H *
        sqrtColumn (fun j => (g j : Unitization ℂ A)) := by
  apply CStarMatrix.ext
  intro i k
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  change φ (∑ j, H 0 j * CFC.sqrt (g j)) =
    ∑ j, φ (H 0 j) * CFC.sqrt (φ (g j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_sqrt_nonneg φ (hg j)]

lemma finiteRowCompression_norm_le_one (H : CStarMatrix (Fin 1) J A) (g : J → A)
    (hH : ‖H‖ ≤ 1) (hg : ∀ j, 0 ≤ g j) (hgsum : ‖∑ j, g j‖ ≤ 1) :
    ‖finiteRowCompression H g‖ ≤ 1 := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hh : ‖rectangularMap φ H‖ ≤ 1 := (rectangularMap_norm_le φ H).trans hH
  have hsum : ‖∑ j, φ (g j)‖ ≤ 1 := by
    rw [← map_sum]
    exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans hgsum
  have hcol : ‖sqrtColumn (fun j => φ (g j))‖ ≤ 1 :=
    sqrtColumn_norm_le_one _ (fun j => map_nonneg φ (hg j)) hsum
  rw [← unitizationOneByOne_norm, unitizationOneByOne_rowCompression H g hg]
  exact norm_row_column_le_one _ _ hh hcol

omit [PartialOrder A] [StarOrderedRing A] [Fintype J] in
lemma unitized_row_relative_offdiagonal (H : CStarMatrix (Fin 1) J A) (b : A)
    (hoff : ∀ i j, i ≠ j → star (H 0 i) * b * H 0 j = 0) :
    let H' := rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H
    ∀ i j, i ≠ j → (H'.conjTranspose * unitizationOneByOne b * H') i j = 0 := by
  dsimp only
  intro i j hij
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  change (∑ k : Fin 1, (∑ l : Fin 1, star (φ (H l i)) * φ b) * φ (H k j)) = 0
  simp only [Fin.sum_univ_one]
  exact rectangularMap_relative_offdiagonal φ H b hoff i j hij

end WeakPureInfiniteness

end

end OAI
