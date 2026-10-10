import OAI.Analysis.PureInfiniteness.SpectralCutReturn
import OAI.Analysis.PureInfiniteness.ScalarSampling
import OAI.Analysis.PureInfiniteness.FiniteCompressionError

namespace OAI

/-! Return of scalar samples through an exact cut Gram matrix. This is the
identity used to preserve the selected elements by the finite compression. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype J] [DecidableEq J]

lemma diagonal_mul_sqrtColumn (c g : J → A) (j : J) (k : Fin 1) :
    (NonunitalGamma.diagonalHom c * sqrtColumn g) j k = c j * CFC.sqrt (g j) := by
  change (∑ l, (if j = l then c j else 0) * CFC.sqrt (g l)) = _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma columnReturn_diagonal (c g : J → A) :
    columnReturn (sqrtColumn g) (NonunitalGamma.diagonalHom c) =
      CStarMatrix.toOneByOne (Fin 1) ℂ A
        (∑ j, star (CFC.sqrt (g j)) * c j * CFC.sqrt (g j)) := by
  unfold columnReturn
  rw [rectangular_mul_assoc]
  ext i k
  change (∑ j, star (CFC.sqrt (g j)) *
    (NonunitalGamma.diagonalHom c * sqrtColumn g : CStarMatrix J (Fin 1) A) j k) =
    ∑ j, star (CFC.sqrt (g j)) * c j * CFC.sqrt (g j)
  simp only [diagonal_mul_sqrtColumn, mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma cut_diagonal_mul_scalarSample (f : J → A) (t : J → ℝ) (δ : ℝ) :
    NonunitalGamma.diagonalHom (fun j => MainGap.cut (f j) δ) * scalarSample (A := A) t =
      NonunitalGamma.diagonalHom (fun j => (t j : ℂ) • MainGap.cut (f j) δ) := by
  unfold scalarSample
  rw [← map_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, mul_smul_comm, mul_one]

lemma columnReturn_cut_sample (f g : J → A) (t : J → ℝ)
    (hf : ∀ j, IsSelfAdjoint (f j)) (hg : ∀ j, 0 ≤ g j)
    (hfg : ∀ j, f j * g j = g j) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    columnReturn (sqrtColumn g)
        (NonunitalGamma.diagonalHom (fun j => MainGap.cut (f j) δ) * scalarSample t) =
      CStarMatrix.toOneByOne (Fin 1) ℂ A ((1 - δ) • ∑ j, (t j : ℂ) • g j) := by
  rw [cut_diagonal_mul_scalarSample, columnReturn_diagonal]
  exact congrArg (CStarMatrix.toOneByOne (Fin 1) ℂ A)
    (spectral_cut_column_return f g hf hg hfg (fun j => (t j : ℂ)) hδ0 hδ1)

lemma finite_cut_compression_preservation (H : CStarMatrix (Fin 1) J A)
    (f g : J → A) (t : J → ℝ) (a : A)
    (hH : ‖H‖ ≤ 1) (hf : ∀ j, IsSelfAdjoint (f j))
    (hg : ∀ j, 0 ≤ g j) (hgsum : ‖∑ j, g j‖ ≤ 1)
    (hfg : ∀ j, f j * g j = g j) (δ r E : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hgram : H.conjTranspose * H = NonunitalGamma.diagonalHom (fun j => MainGap.cut (f j) δ))
    (hmoment : ‖(∑ j, (t j : ℂ) • g j) - a‖ ≤ r)
    (hrow : ‖CStarMatrix.toOneByOne (Fin 1) ℂ A a * H - H * scalarSample t‖ ≤ E) :
    let d := H * sqrtColumn g
    ‖d.conjTranspose * CStarMatrix.toOneByOne (Fin 1) ℂ A a * d -
      CStarMatrix.toOneByOne (Fin 1) ℂ A a‖ ≤ E + (r + δ * (‖a‖ + r)) := by
  apply norm_finite_compression_preservation H (sqrtColumn g) hH
    (sqrtColumn_norm_le_one g hg hgsum) _ (scalarSample t) E _ hrow
  rw [hgram, columnReturn_cut_sample f g t hf hg hfg hδ0 hδ1]
  let e := (CStarMatrix.toOneByOne (Fin 1) ℂ A).toNonUnitalStarAlgHom
  change ‖e ((1 - δ) • ∑ j, (t j : ℂ) • g j) - e a‖ ≤ _
  rw [← map_sub]
  exact (NonUnitalStarAlgHom.norm_map e
    (CStarMatrix.toOneByOne (Fin 1) ℂ A).injective _).trans_le
    (norm_scaled_reconstruction_error a _ r δ hmoment hδ0)

end WeakPureInfiniteness

end

end OAI
