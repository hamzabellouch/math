import OAI.Analysis.PureInfiniteness.CrossCompressionEstimate

namespace OAI

/-! Orthogonal spectral return columns give small mixed compressions in the
original nonunital algebra. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {D J : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [Fintype J] [DecidableEq J]

lemma disjoint_columns_cross_diagonal_zero (g k c : J → D)
    (hdisj : ∀ j, g j = 0 ∨ k j = 0) :
    (sqrtColumn g).conjTranspose * NonunitalGamma.diagonalHom c * sqrtColumn k = 0 := by
  rw [rectangular_mul_assoc]
  apply CStarMatrix.ext
  intro r s
  change (∑ j, star (CFC.sqrt (g j)) *
    (NonunitalGamma.diagonalHom c * sqrtColumn k) j s) = 0
  simp only [diagonal_mul_sqrtColumn]
  apply Finset.sum_eq_zero
  intro j _
  rcases hdisj j with h | h <;> simp [h]

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizationOneByOne_cross_norm (u a v : A) :
    ‖(unitizationOneByOne u).conjTranspose * unitizationOneByOne a * unitizationOneByOne v‖ =
      ‖star u * a * v‖ := by
  change ‖star (unitizationOneByOne u) * unitizationOneByOne a * unitizationOneByOne v‖ = _
  rw [← map_star, ← map_mul, ← map_mul, unitizationOneByOne_norm]

lemma nonunital_cross_compression_norm_le (H : CStarMatrix (Fin 1) J A)
    (f g k : J → A) (t : J → ℝ) (a : A) (δ E : ℝ) (hδ : 0 ≤ δ)
    (hH : ‖H‖ ≤ 1) (hf : ∀ j, 0 ≤ f j) (hg : ∀ j, 0 ≤ g j) (hk : ∀ j, 0 ≤ k j)
    (hgsum : ‖∑ j, g j‖ ≤ 1) (hksum : ‖∑ j, k j‖ ≤ 1)
    (hdisj : ∀ j, g j = 0 ∨ k j = 0)
    (hgram : H.conjTranspose * H = NonunitalGamma.diagonalHom (fun j => MainGap.cut (f j) δ))
    (hrow : ‖unitizationOneByOne a * rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H -
      rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H * scalarSample t‖ ≤ E) :
    ‖star (finiteRowCompression H g) * a * finiteRowCompression H k‖ ≤ E := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hH' : ‖rectangularMap φ H‖ ≤ 1 := (rectangularMap_norm_le φ H).trans hH
  have hgn : ‖sqrtColumn (fun j => φ (g j))‖ ≤ 1 := by
    apply sqrtColumn_norm_le_one _ (fun j => map_nonneg φ (hg j))
    rw [← map_sum]
    exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans hgsum
  have hkn : ‖sqrtColumn (fun j => φ (k j))‖ ≤ 1 := by
    apply sqrtColumn_norm_le_one _ (fun j => map_nonneg φ (hk j))
    rw [← map_sum]
    exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans hksum
  have hzero := disjoint_columns_cross_diagonal_zero (fun j => φ (g j))
    (fun j => φ (k j)) (fun j => (t j : ℂ) • MainGap.cut (φ (f j)) δ) (by
      intro j
      rcases hdisj j with h | h
      · exact Or.inl (by rw [h, map_zero])
      · exact Or.inr (by rw [h, map_zero]))
  have he := norm_cross_compression_error (rectangularMap φ H)
    (sqrtColumn (fun j => φ (g j))) (sqrtColumn (fun j => φ (k j)))
    hH' hgn hkn (unitizationOneByOne a) (scalarSample t)
  rw [rectangularMap_gram_cut φ H f hf δ hδ hgram, cut_diagonal_mul_scalarSample,
    hzero, sub_zero] at he
  have hdg : unitizationOneByOne (finiteRowCompression H g) =
      rectangularMap φ H * sqrtColumn (fun j => φ (g j)) :=
    unitizationOneByOne_rowCompression H g hg
  have hdk : unitizationOneByOne (finiteRowCompression H k) =
      rectangularMap φ H * sqrtColumn (fun j => φ (k j)) :=
    unitizationOneByOne_rowCompression H k hk
  rw [← hdg, ← hdk, unitizationOneByOne_cross_norm] at he
  exact he.trans hrow

end WeakPureInfiniteness

end

end OAI
