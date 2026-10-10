import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Pencil

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m p : ℕ}

lemma vector_eq_sum_single {R : Type*} [Semiring R] (x : Fin n → R) :
    x=∑ i : Fin n,x i • (Pi.single i 1 : Fin n → R) := by
  classical
  ext j
  simp [Pi.single_apply]

def Pencil.ofAffine (C : Matrix (Fin m) (Fin m) ℚ)
    (L : (Fin n → ℚ) →ₗ[ℚ] Matrix (Fin m) (Fin m) ℚ)
    (hC : C.IsSymm) (hL : ∀ y,(L y).IsSymm) : Pencil n m where
  constant := C
  coeff i := L (Pi.single i 1)
  symmetric_constant := hC
  symmetric_coeff index := hL (Pi.single index 1)

lemma Pencil.ofAffine_eval (C : Matrix (Fin m) (Fin m) ℚ)
    (L : (Fin n → ℚ) →ₗ[ℚ] Matrix (Fin m) (Fin m) ℚ)
    (hC : C.IsSymm) (hL : ∀ y,(L y).IsSymm) (y : Fin n → ℚ) :
    (Pencil.ofAffine C L hC hL).eval y=C+L y := by
  change C+∑ i,y i • L (Pi.single i 1)=C+L y
  congr 1
  conv_rhs => rw [vector_eq_sum_single y]
  simp

def blockDiagonal {R : Type*} [Zero R] (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin p) (Fin p) R) : Matrix (Fin (m+p)) (Fin (m+p)) R :=
  (Matrix.fromBlocks A 0 0 B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

lemma blockDiagonal_symm {R : Type*} [AddMonoid R] (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin p) (Fin p) R) (hA : A.IsSymm) (hB : B.IsSymm) :
    (blockDiagonal A B).IsSymm :=
  (Matrix.IsSymm.fromBlocks hA (by simp) hB).submatrix _

lemma blockDiagonal_posSemidef (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin p) (Fin p) ℝ) :
    (blockDiagonal A B).PosSemidef ↔ A.PosSemidef ∧ B.PosSemidef := by
  let C := Matrix.fromBlocks A (0 : Matrix (Fin m) (Fin p) ℝ) 0 B
  have he : (blockDiagonal A B).PosSemidef ↔ C.PosSemidef := by
    constructor
    · intro h
      have hd := h.submatrix (fun i : Fin m ⊕ Fin p => finSumFinEquiv i)
      simp only [blockDiagonal,Matrix.submatrix_submatrix,Function.comp_def,
        Equiv.symm_apply_apply] at hd
      exact hd
    · exact fun h => h.submatrix _
  rw [he]
  constructor
  · intro h
    exact ⟨h.submatrix (Sum.inl : Fin m → Fin m ⊕ Fin p),h.submatrix (Sum.inr : Fin p → Fin m ⊕ Fin p)⟩
  · rintro ⟨hA,hB⟩
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_,?_⟩
    · apply Matrix.isHermitian_fromBlocks_iff.mpr
      exact ⟨hA.isHermitian,by simp,by simp,hB.isHermitian⟩
    · intro x
      have ha := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
      have hb := hB.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
      simpa only [C,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,add_zero,zero_add,
        dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.star_apply,
        star_trivial,Function.comp_def] using add_nonneg ha hb

lemma blockDiagonal_realMap (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin p) (Fin p) ℚ) :
    (blockDiagonal A B).map (fun x => (x:ℝ)) =
      blockDiagonal (A.map (fun x => (x:ℝ))) (B.map (fun x => (x:ℝ))) := by
  ext i j
  change ((Matrix.fromBlocks A 0 0 B) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j):ℝ)=_
  change _=(Matrix.fromBlocks (A.map (fun x => (x:ℝ))) 0 0 (B.map (fun x => (x:ℝ))))
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp

def Pencil.blockDiagonal (A : Pencil n m) (B : Pencil n p) : Pencil n (m+p) where
  constant := CurrentKS.RationalSDP.blockDiagonal A.constant B.constant
  coeff i := CurrentKS.RationalSDP.blockDiagonal (A.coeff i) (B.coeff i)
  symmetric_constant := blockDiagonal_symm _ _ A.symmetric_constant B.symmetric_constant
  symmetric_coeff i := blockDiagonal_symm _ _ (A.symmetric_coeff i) (B.symmetric_coeff i)

lemma Pencil.blockDiagonal_realEval (A : Pencil n m) (B : Pencil n p) (z : Fin n → ℝ) :
    (A.blockDiagonal B).realEval z = CurrentKS.RationalSDP.blockDiagonal (A.realEval z) (B.realEval z) := by
  ext i j
  simp only [Pencil.realEval,Pencil.blockDiagonal,blockDiagonal_realMap,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [CurrentKS.RationalSDP.blockDiagonal,hi,hj,Matrix.sum_apply]

end CurrentKS.RationalSDP

end OAI
