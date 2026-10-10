import OAI.Analysis.KadisonKastler.BoundedSequence
import Mathlib.Analysis.Normed.Lp.lpSpace

namespace OAI

/-! # Bounded products for the finite-matrix model

The matrix sizes in the preliminary free model vary with the coordinate.
The existing `lp` space at infinity supplies its ordinary bounded-product
C*-algebra, without identifying the operator norm with a tracial norm.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable (B : ℕ → Type u) [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

abbrev VaryingBoundedSequence := lp B (⊤ : ENNReal)

instance varyingSequenceCStarAlgebra : CStarAlgebra (VaryingBoundedSequence B) where
  __ := lp.inftyNormedRing (B := B)
  __ := lp.inftyStarRing (B := B)
  __ := lp.inftyCStarRing (B := B)
  __ := lp.inftyNormedAlgebra (𝕜 := ℂ) (B := B)
  __ := (inferInstance : CompleteSpace (lp B (⊤ : ENNReal)))
  __ := (inferInstance : StarModule ℂ (lp B (⊤ : ENNReal)))

/-- Evaluation in the j-th finite factor. -/
def varyingSequenceEval (j : ℕ) : VaryingBoundedSequence B →⋆ₐ[ℂ] B j where
  toFun x := x j
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

variable {B}

omit [∀ j, Nontrivial (B j)] in
theorem varyingSequence_norm_apply_le (x : VaryingBoundedSequence B) (j : ℕ) :
    ‖x j‖ ≤ ‖x‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero x j

variable {C : Type v} [CStarAlgebra C]

/-- Coordinate star embeddings into a fixed factor induce the map on
bounded products used for the finite-matrix model. -/
def varyingSequenceMap (φ : ∀ j, B j →⋆ₐ[ℂ] C) :
    VaryingBoundedSequence B →⋆ₐ[ℂ] BoundedSequence C where
  toFun x := BoundedContinuousFunction.mkOfDiscrete (fun j => φ j (x j)) (2 * ‖x‖) (by
    intro i j
    calc
      dist (φ i (x i)) (φ j (x j)) ≤ ‖φ i (x i)‖ + ‖φ j (x j)‖ := dist_le_norm_add_norm _ _
      _ ≤ ‖x i‖ + ‖x j‖ := add_le_add (NonUnitalStarAlgHom.norm_apply_le (φ i) _)
        (NonUnitalStarAlgHom.norm_apply_le (φ j) _)
      _ ≤ 2 * ‖x‖ := by linarith [varyingSequence_norm_apply_le x i, varyingSequence_norm_apply_le x j])
  map_one' := by apply BoundedContinuousFunction.ext; intro j; exact map_one (φ j)
  map_mul' x y := by apply BoundedContinuousFunction.ext; intro j; exact map_mul (φ j) (x j) (y j)
  map_zero' := by apply BoundedContinuousFunction.ext; intro j; exact map_zero (φ j)
  map_add' x y := by apply BoundedContinuousFunction.ext; intro j; exact map_add (φ j) (x j) (y j)
  commutes' c := by apply BoundedContinuousFunction.ext; intro j; exact (φ j).commutes c
  map_star' x := by apply BoundedContinuousFunction.ext; intro j; exact map_star (φ j) (x j)

@[simp]
theorem varyingSequenceMap_apply (φ : ∀ j, B j →⋆ₐ[ℂ] C)
    (x : VaryingBoundedSequence B) (j : ℕ) : varyingSequenceMap φ x j = φ j (x j) := rfl

end

end KadisonKastler

end OAI
