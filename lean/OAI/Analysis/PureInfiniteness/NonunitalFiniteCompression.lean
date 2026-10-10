import OAI.Analysis.PureInfiniteness.CompressionNorms
import OAI.Analysis.PureInfiniteness.MappedSpectralEstimates

namespace OAI

/-! Finite spectral compression estimates in the original nonunital algebra.
Scalar sampling takes place only after the faithful unitization embedding. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A J : Type*} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A] [Fintype J] [DecidableEq J]

lemma nonunital_finite_compression_preservation
    (H : CStarMatrix (Fin 1) J A) (f g : J → A) (t : J → ℝ) (a : A)
    (hH : ‖H‖ ≤ 1) (hf : ∀ j, 0 ≤ f j) (hg : ∀ j, 0 ≤ g j)
    (hgsum : ‖∑ j, g j‖ ≤ 1) (hfg : ∀ j, f j * g j = g j)
    (δ r E : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hgram : H.conjTranspose * H = NonunitalGamma.diagonalHom (fun j => MainGap.cut (f j) δ))
    (hmoment : ‖a - ∑ j, (t j : ℂ) • g j‖ ≤ r)
    (hrow : ‖unitizationOneByOne a * rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H -
      rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H * scalarSample t‖ ≤ E) :
    let d := finiteRowCompression H g
    ‖star d * a * d - a‖ ≤ E + (r + δ * (‖a‖ + r)) := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hH' : ‖rectangularMap φ H‖ ≤ 1 := (rectangularMap_norm_le φ H).trans hH
  have hgsum' : ‖∑ j, φ (g j)‖ ≤ 1 := by
    rw [← map_sum]
    exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans hgsum
  have hfg' : ∀ j, φ (f j) * φ (g j) = φ (g j) := by
    intro j
    rw [← map_mul, hfg]
  have hm := mapped_moment_norm_le φ a g (fun j => (t j : ℂ)) r hmoment
  have he := finite_cut_compression_preservation (rectangularMap φ H)
    (fun j => φ (f j)) (fun j => φ (g j)) t (φ a) hH'
    (fun j => (map_nonneg φ (hf j)).isSelfAdjoint) (fun j => map_nonneg φ (hg j))
    hgsum' hfg' δ r E hδ0 hδ1 (rectangularMap_gram_cut φ H f hf δ hδ0 hgram)
    (by simpa only [norm_sub_rev] using hm) hrow
  dsimp only at he ⊢
  have hd : unitizationOneByOne (finiteRowCompression H g) =
      rectangularMap φ H * sqrtColumn (fun j => φ (g j)) :=
    unitizationOneByOne_rowCompression H g hg
  rw [← hd] at he
  change ‖(unitizationOneByOne (finiteRowCompression H g)).conjTranspose *
    unitizationOneByOne a * unitizationOneByOne (finiteRowCompression H g) -
    unitizationOneByOne a‖ ≤ _ at he
  rw [unitizationOneByOne_compression_norm] at he
  exact he.trans_eq (by rw [show ‖φ a‖ = ‖a‖ from Unitization.norm_inr a])

lemma nonunital_finite_compression_commutator
    (H : CStarMatrix (Fin 1) J A) (hH : ‖H‖ ≤ 1)
    (g : J → A) (hg : ∀ j, 0 ≤ g j) (hgsum : ‖∑ j, g j‖ ≤ 1)
    (t : J → ℝ) (a b : A) (hb : IsSelfAdjoint b)
    (hoff : ∀ i j, i ≠ j → star (H 0 i) * b * H 0 j = 0)
    (r q : ℝ) (hfirst : ‖a - ∑ j, (t j : ℂ) • g j‖ ≤ r)
    (hsecond : ‖a * a - ∑ j, (((t j) ^ 2 : ℝ) : ℂ) • g j‖ ≤ q) :
    let d := finiteRowCompression H g
    ‖a * (star d * b * d) - (star d * b * d) * a‖ ≤
      (2 * r + 2 * Real.sqrt (q + r * (2 * ‖a‖ + r))) * ‖b‖ := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hH' : ‖rectangularMap φ H‖ ≤ 1 := (rectangularMap_norm_le φ H).trans hH
  have hgsum' : ‖∑ j, φ (g j)‖ ≤ 1 := by
    rw [← map_sum]
    exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans hgsum
  have hg' : ∀ j, 0 ≤ φ (g j) := fun j => map_nonneg φ (hg j)
  have hfirst' := mapped_moment_norm_le φ a g (fun j => (t j : ℂ)) r hfirst
  have hsecond' := mapped_moment_norm_le φ (a * a) g
    (fun j => (((t j) ^ 2 : ℝ) : ℂ)) q hsecond
  have he := finite_spectral_compression_commutator (rectangularMap φ H) hH'
    (fun j => φ (g j)) hg' hgsum' t (unitizationOneByOne a) (unitizationOneByOne b)
    (show star (unitizationOneByOne b) = unitizationOneByOne b by rw [← map_star, hb.star_eq])
    (unitized_row_relative_offdiagonal H b hoff) r q
    (by change ‖columnReturn _ _ - CStarMatrix.toOneByOne (Fin 1) ℂ (Unitization ℂ A) (φ a)‖ ≤ r
        rw [scalarSample_first_moment_norm _ _ hg']
        simpa only [norm_sub_rev] using hfirst')
    (by change ‖columnReturn _ _ - CStarMatrix.toOneByOne (Fin 1) ℂ (Unitization ℂ A) (φ a) *
          CStarMatrix.toOneByOne (Fin 1) ℂ (Unitization ℂ A) (φ a)‖ ≤ q
        rw [scalarSample_second_moment_norm _ _ hg']
        simpa only [map_mul, norm_sub_rev] using hsecond')
  dsimp only at he ⊢
  have hd : unitizationOneByOne (finiteRowCompression H g) =
      rectangularMap φ H * sqrtColumn (fun j => φ (g j)) :=
    unitizationOneByOne_rowCompression H g hg
  rw [← hd] at he
  have hconj (d : A) : (unitizationOneByOne d).conjTranspose * unitizationOneByOne b *
      unitizationOneByOne d = unitizationOneByOne (star d * b * d) := by
    change star (unitizationOneByOne d) * unitizationOneByOne b * unitizationOneByOne d = _
    rw [← map_star, ← map_mul, ← map_mul]
  rw [hconj, unitizationOneByOne_commutator_norm, unitizationOneByOne_norm,
    unitizationOneByOne_norm] at he
  exact he

end WeakPureInfiniteness

end

end OAI
