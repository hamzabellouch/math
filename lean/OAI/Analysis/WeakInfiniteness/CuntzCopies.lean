import Mathlib
import OAI.Analysis.WeakInfiniteness.ElementaryComparison

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] [Fintype k] [Fintype l] in
lemma continuous_blockSum : Continuous (fun p : CStarMatrix m m A × CStarMatrix n n A => blockSum p.1 p.2) := by
  change Continuous (fun p : Matrix m m A × Matrix n n A => Matrix.fromBlocks p.1 0 0 p.2)
  exact continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd

lemma CuntzSubequiv.blockSum {a : CStarMatrix m m A} {b : CStarMatrix n n A}
    {c : CStarMatrix k k A} {d : CStarMatrix l l A}
    (hab : CuntzSubequiv a b) (hcd : CuntzSubequiv c d) :
    CuntzSubequiv (blockSum a c) (blockSum b d) := by
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_blockSum (m := m) (n := k) (A := A)).continuousAt ε hε
  obtain ⟨v, hv⟩ := hab δ hδ
  obtain ⟨w, hw⟩ := hcd δ hδ
  let V : CStarMatrix (n ⊕ l) (m ⊕ k) A := Matrix.fromBlocks v 0 0 w
  refine ⟨V, ?_⟩
  have he : V.conjTranspose*WeakPureInfiniteness.blockSum b d*V = WeakPureInfiniteness.blockSum (v.conjTranspose*b*v) (w.conjTranspose*d*w) := by
    change (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm v) 0 0 (CStarMatrix.ofMatrix.symm w)).conjTranspose *
      Matrix.fromBlocks (CStarMatrix.ofMatrix.symm b) 0 0 (CStarMatrix.ofMatrix.symm d) * Matrix.fromBlocks (CStarMatrix.ofMatrix.symm v) 0 0 (CStarMatrix.ofMatrix.symm w) =
        Matrix.fromBlocks ((CStarMatrix.ofMatrix.symm v).conjTranspose*(CStarMatrix.ofMatrix.symm b)*(CStarMatrix.ofMatrix.symm v)) 0 0
          ((CStarMatrix.ofMatrix.symm w).conjTranspose*(CStarMatrix.ofMatrix.symm d)*(CStarMatrix.ofMatrix.symm w))
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [he]
  have hp : dist (v.conjTranspose*b*v, w.conjTranspose*d*w) (a,c) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (by simpa only [dist_eq_norm] using hv) (by simpa only [dist_eq_norm] using hw)
  simpa only [dist_eq_norm] using hcont hp

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] [Fintype k] [Fintype l] in
def matrixSubmatrix (e : m → n) (f : k → l) (M : CStarMatrix n l A) : CStarMatrix m k A :=
  fun i j => M (e i) (f j)

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] [Fintype k] [Fintype l] in
lemma continuous_matrixSubmatrix (e : m → n) (f : k → l) : Continuous (matrixSubmatrix (A := A) e f) := by
  change Continuous (fun M : Matrix n l A => M.submatrix e f)
  fun_prop

lemma CuntzSubequiv.submatrix_left {a : CStarMatrix n n A} {b : CStarMatrix k k A}
    (hab : CuntzSubequiv a b) (e : m → n) : CuntzSubequiv (matrixSubmatrix e e a) b := by
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_matrixSubmatrix (A := A) e e).continuousAt ε hε
  obtain ⟨v, hv⟩ := hab δ hδ
  refine ⟨matrixSubmatrix id e v, ?_⟩
  have he : (matrixSubmatrix id e v).conjTranspose*b*matrixSubmatrix id e v =
      matrixSubmatrix e e (v.conjTranspose*b*v) := by
    ext i j
    simp only [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply, matrixSubmatrix, id_eq]
  rw [he]
  simpa only [dist_eq_norm] using hcont (by simpa only [dist_eq_norm] using hv)

lemma CuntzSubequiv.reindex_right {a : CStarMatrix m m A} {b : CStarMatrix n n A}
    (hab : CuntzSubequiv a b) (e : k ≃ n) : CuntzSubequiv a (matrixSubmatrix e e b) := by
  have h := (cuntzSubequiv_refl (matrixSubmatrix e e b)).submatrix_left e.symm
  have he : matrixSubmatrix e.symm e.symm (matrixSubmatrix e e b) = b := by
    ext i j
    simp only [matrixSubmatrix, Equiv.apply_symm_apply]
  rw [he] at h
  exact hab.trans h

omit [PartialOrder A] [StarOrderedRing A] in
lemma diagonalCopies_submatrix (a : A) {d r : ℕ} (e : Fin d → Fin r)
    (he : Function.Injective e) : matrixSubmatrix e e (diagonalCopies r a) = diagonalCopies d a := by
  ext i j
  simp only [matrixSubmatrix, diagonalCopies, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply]
  simp only [he.eq_iff]

lemma diagonalCopies_cuntzSubequiv (a : A) {d r : ℕ} (hdr : d ≤ r) :
    CuntzSubequiv (diagonalCopies d a) (diagonalCopies r a) := by
  have h := (cuntzSubequiv_refl (diagonalCopies r a)).submatrix_left (Fin.castLE hdr)
  rwa [diagonalCopies_submatrix a _ (Fin.castLE_injective hdr)] at h

omit [PartialOrder A] [StarOrderedRing A] in
lemma diagonalCopies_double (a : A) (r : ℕ) :
    matrixSubmatrix (finSumFinEquiv.symm : Fin (r+r) → Fin r ⊕ Fin r)
      finSumFinEquiv.symm (blockSum (diagonalCopies r a) (diagonalCopies r a)) =
        diagonalCopies (r+r) a := by
  classical
  change (Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin r => a)) 0 0
    (Matrix.diagonal (fun _ : Fin r => a))).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
      Matrix.diagonal (fun _ : Fin (r+r) => a)
  rw [Matrix.fromBlocks_diagonal]
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  cases finSumFinEquiv.symm i <;> rfl

lemma ProperlyInfinite.diagonal_powers {a : A} {n : ℕ}
    (hpi : ProperlyInfinite (diagonalCopies n a)) (k : ℕ) :
    CuntzSubequiv (diagonalCopies (2^k*n) a) (diagonalCopies n a) := by
  induction k with
  | zero =>
    exact diagonalCopies_cuntzSubequiv a (by simp)
  | succ k ih =>
    have h := (ih.blockSum ih).trans hpi
    have h' := h.submatrix_left (finSumFinEquiv.symm : Fin (2^k*n+2^k*n) → _)
    rw [diagonalCopies_double] at h'
    exact (diagonalCopies_cuntzSubequiv a (show 2^(k+1)*n ≤ 2^k*n+2^k*n by
      rw [pow_succ]; nlinarith)).trans h'

lemma ProperlyInfinite.diagonal_absorbs {a : A} {n : ℕ} (hn : 1 ≤ n)
    (hpi : ProperlyInfinite (diagonalCopies n a)) (d : ℕ) :
    CuntzSubequiv (diagonalCopies d a) (diagonalCopies n a) := by
  have hd : d ≤ 2^d*n := calc
    d ≤ 2^d := (Nat.lt_two_pow_self (n := d)).le
    _ ≤ 2^d*n := by simpa only [mul_one] using Nat.mul_le_mul_left (2^d) hn
  exact (diagonalCopies_cuntzSubequiv a hd).trans (hpi.diagonal_powers d)

end

end WeakPureInfiniteness
end

end OAI
