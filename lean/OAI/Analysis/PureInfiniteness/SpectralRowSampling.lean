import OAI.Analysis.PureInfiniteness.SpectralRowEstimate
import OAI.Analysis.PureInfiniteness.ScalarSampling

namespace OAI

/-! The sampled row identity connecting the spectral partition with its actual
finite compression. It also controls the square using the same row error. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace WeakPureInfiniteness

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype J] [DecidableEq J]

omit [PartialOrder A] [StarOrderedRing A] in
lemma row_mul_scalarSample (H : CStarMatrix (Fin 1) J A) (t : J → ℝ) (i : Fin 1) (j : J) :
    (H * scalarSample (A := A) t : CStarMatrix (Fin 1) J A) i j = (t j : ℂ) • H i j := by
  change (∑ l, H i l * (if l = j then (t l : ℂ) • (1 : A) else 0)) = _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    mul_smul_comm, mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
lemma row_mul_coefficientDiagonal (H : CStarMatrix (Fin 1) J A) (d : J → A)
    (i : Fin 1) (j : J) :
    (H * NonunitalGamma.diagonalHom d) i j = H i j * d j := by
  change (∑ l, H i l * (if l = j then d l else 0)) = _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma sampled_row_error_identity (a : A) (f d : J → A) (t : J → ℝ)
    (H : CStarMatrix (Fin 1) J A) (hH : ∀ j, H 0 j = CFC.sqrt (f j) * d j) :
    CStarMatrix.toOneByOne (Fin 1) ℂ A a * H - H * scalarSample t =
      sampledErrorRow a f t * NonunitalGamma.diagonalHom d := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [CStarMatrix.sub_apply, row_mul_scalarSample, row_mul_coefficientDiagonal]
  change (∑ k : Fin 1, a * H k j) - (t j : ℂ) • H 0 j = _
  rw [Fin.sum_univ_one, hH]
  change a * (CFC.sqrt (f j) * d j) - (t j : ℂ) • (CFC.sqrt (f j) * d j) =
    (a * CFC.sqrt (f j) - (t j : ℂ) • CFC.sqrt (f j)) * d j
  rw [sub_mul, smul_mul_assoc, mul_assoc]

lemma sampled_row_error_norm_le (a : A) (f d : J → A) (t : J → ℝ)
    (H : CStarMatrix (Fin 1) J A) (hH : ∀ j, H 0 j = CFC.sqrt (f j) * d j)
    (ha : IsSelfAdjoint a) (hf : ∀ j, 0 ≤ f j) (haf : ∀ j, Commute a (f j))
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hd : ∀ j, ‖d j‖ ≤ C)
    (herr : ‖∑ j, sampledQuadraticError a (f j) (t j)‖ ≤ q ^ 2) :
    ‖CStarMatrix.toOneByOne (Fin 1) ℂ A a * H - H * scalarSample t‖ ≤ q * C := by
  rw [sampled_row_error_identity a f d t H hH]
  exact sampledErrorRow_coeff_norm_le a f t d ha hf haf C q hC hq hd herr

omit [DecidableEq J] in
lemma squared_row_error_norm_le (a : CStarMatrix (Fin 1) (Fin 1) A)
    (H : CStarMatrix (Fin 1) J A) (S : CStarMatrix J J A) :
    ‖(a * a) * H - H * (S * S)‖ ≤ (‖a‖ + ‖S‖) * ‖a * H - H * S‖ := by
  have he : (a * a) * H - H * (S * S) =
      a * (a * H - H * S) + (a * H - H * S) * S := by
    rw [rectangular_mul_sub, rectangular_sub_mul]
    simp only [rectangular_mul_assoc]
    abel
  rw [he]
  calc
    _ ≤ ‖a * (a * H - H * S)‖ + ‖(a * H - H * S) * S‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖a * H - H * S‖ + ‖a * H - H * S‖ * ‖S‖ :=
      add_le_add (rectangular_norm_mul_le _ _) (rectangular_norm_mul_le _ _)
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
