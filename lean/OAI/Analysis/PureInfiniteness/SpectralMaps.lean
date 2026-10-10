import OAI.Analysis.PureInfiniteness.RectangularMaps
import OAI.Analysis.PureInfiniteness.ScalarSampling
import OAI.Analysis.PureInfiniteness.UltrapowerRelativeGram

namespace OAI

/-! Transport of the finite Gram data through the original algebra's
unitization map. No pure-infiniteness assumption is imposed on the unitization. -/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma map_sqrt_nonneg (φ : A →⋆ₙₐ[ℂ] B) {a : A} (ha : 0 ≤ a) :
    φ (CFC.sqrt a) = CFC.sqrt (φ a) :=
  φ.map_cfcₙ NNReal.sqrt a NNReal.continuous_sqrt.continuousOn NNReal.sqrt_zero
    (map_continuous φ) ha (map_nonneg φ ha)

lemma rectangularMap_gram_cut (φ : A →⋆ₙₐ[ℂ] B) {J : Type*}
    [Fintype J] [DecidableEq J] (H : CStarMatrix (Fin 1) J A) (f : J → A)
    (hf : ∀ j, 0 ≤ f j) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : H.conjTranspose * H = NonunitalGamma.diagonalHom (fun j => MainGap.cut (f j) δ)) :
    (rectangularMap φ H).conjTranspose * rectangularMap φ H =
      NonunitalGamma.diagonalHom (fun j => MainGap.cut (φ (f j)) δ) := by
  rw [← rectangularMap_conjTranspose, ← rectangularMap_mul, hgram,
    rectangularMap_diagonal]
  congr 1
  funext j
  exact MainGap.map_cut φ (hf j) hδ

lemma rectangularMap_row_factor (φ : A →⋆ₙₐ[ℂ] B) {J : Type*}
    (H : CStarMatrix (Fin 1) J A) (f d : J → A) (hf : ∀ j, 0 ≤ f j)
    (hentry : ∀ j, H 0 j = CFC.sqrt (f j) * d j) (j : J) :
    rectangularMap φ H 0 j = CFC.sqrt (φ (f j)) * φ (d j) := by
  change φ (H 0 j) = _
  rw [hentry, map_mul, map_sqrt_nonneg φ (hf j)]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma rectangularMap_relative_offdiagonal (φ : A →⋆ₙₐ[ℂ] B) {J : Type*}
    (H : CStarMatrix (Fin 1) J A) (b : A)
    (hoff : ∀ i j, i ≠ j → star (H 0 i) * b * H 0 j = 0) :
    ∀ i j, i ≠ j →
      star (rectangularMap φ H 0 i) * φ b * rectangularMap φ H 0 j = 0 := by
  intro i j hij
  change star (φ (H 0 i)) * φ b * φ (H 0 j) = 0
  rw [← map_star, ← map_mul, ← map_mul, hoff i j hij, map_zero]

end WeakPureInfiniteness

end

end OAI
