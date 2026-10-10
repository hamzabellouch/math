import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Pencil

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m : ℕ}

def blockScalar {R : Type*} [Zero R] (A : Matrix (Fin m) (Fin m) R) (b : R) :
    Matrix (Fin (m+1)) (Fin (m+1)) R :=
  (Matrix.fromBlocks A 0 0 (Matrix.of fun (_ _ : Fin 1) => b)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

lemma blockScalar_symm (A : Matrix (Fin m) (Fin m) ℚ) (hA : A.IsSymm) (b : ℚ) :
    (blockScalar A b).IsSymm := by
  exact (Matrix.IsSymm.fromBlocks hA (by simp) (by rfl)).submatrix _

lemma blockScalar_posSemidef (A : Matrix (Fin m) (Fin m) ℝ) (b : ℝ) :
    (blockScalar A b).PosSemidef ↔ A.PosSemidef ∧ 0 ≤ b := by
  let C := Matrix.fromBlocks A (0 : Matrix (Fin m) (Fin 1) ℝ) 0 (Matrix.of fun (_ _ : Fin 1) => b)
  have he : (blockScalar A b).PosSemidef ↔ C.PosSemidef := by
    constructor
    · intro h
      have hd := h.submatrix (fun i : Fin m ⊕ Fin 1 => finSumFinEquiv i)
      simp only [blockScalar,Matrix.submatrix_submatrix,Function.comp_def,
        Equiv.symm_apply_apply] at hd
      exact hd
    · exact fun h => h.submatrix _
  rw [he]
  constructor
  · intro h
    have hA := h.submatrix (Sum.inl : Fin m → Fin m ⊕ Fin 1)
    have hb := h.submatrix (Sum.inr : Fin 1 → Fin m ⊕ Fin 1)
    refine ⟨by simp only [C,Matrix.submatrix,Matrix.fromBlocks_apply₁₁] at hA; exact hA,?_⟩
    have hh := hb.diag_nonneg (i := (0 : Fin 1))
    exact hh
  · rintro ⟨hA,hb⟩
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_,?_⟩
    · apply Matrix.isHermitian_fromBlocks_iff.mpr
      exact ⟨hA.isHermitian,by simp,by simp,by ext i j; simp⟩
    · intro x
      have hh := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
      simp only [dotProduct,Pi.star_apply,star_trivial,Function.comp_def] at hh
      change 0 ≤ ∑ i : Fin m, x (Sum.inl i)*(A *ᵥ (x ∘ Sum.inl)) i at hh
      have hs : 0 ≤ b*(x (Sum.inr 0))^2 := mul_nonneg hb (sq_nonneg _)
      simpa only [C,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,add_zero,zero_add,
        dotProduct, Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.star_apply,star_trivial,
        Function.comp_def,Matrix.mulVec,Fin.sum_univ_one,Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply,Matrix.of_apply,zero_mul,Finset.sum_const_zero] using show
          0 ≤ (∑ i : Fin m, x (Sum.inl i)*(A *ᵥ (x ∘ Sum.inl)) i)+
            x (Sum.inr 0)*(b*x (Sum.inr 0)) by nlinarith

lemma blockScalar_realMap (A : Matrix (Fin m) (Fin m) ℚ) (b : ℚ) :
    (blockScalar A b).map (fun x => (x:ℝ)) =
      blockScalar (A.map (fun x => (x:ℝ))) (b:ℝ) := by
  ext i j
  change ((Matrix.fromBlocks A 0 0 (Matrix.of fun (_ _ : Fin 1) => b))
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) : ℝ) = _
  change _ = (Matrix.fromBlocks (A.map (fun x => (x:ℝ))) 0 0 (Matrix.of fun (_ _ : Fin 1) => (b:ℝ)))
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp

def Pencil.withLevel (B : Pencil n m) (f : Fin n → ℚ) (q : ℚ) : Pencil n (m+1) where
  constant := blockScalar B.constant q
  coeff i := blockScalar (B.coeff i) (-f i)
  symmetric_constant := blockScalar_symm _ B.symmetric_constant _
  symmetric_coeff i := blockScalar_symm _ (B.symmetric_coeff i) _

lemma Pencil.withLevel_realEval (B : Pencil n m) (f : Fin n → ℚ) (q : ℚ) (z : Fin n → ℝ) :
    (B.withLevel f q).realEval z =
      blockScalar (B.realEval z) ((q:ℝ)-(fun i => (f i:ℝ)) ⬝ᵥ z) := by
  ext i j
  simp only [Pencil.realEval,Pencil.withLevel,blockScalar_realMap,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [blockScalar,hi,hj,Matrix.sum_apply,dotProduct,mul_comm,sub_eq_add_neg]

lemma Pencil.withLevel_feasible (B : Pencil n m) (f : Fin n → ℚ) (q : ℚ)
    (z : EuclideanSpace ℝ (Fin n)) :
    ((B.withLevel f q).realEval z).PosSemidef ↔ (B.realEval z).PosSemidef ∧
      (fun i => (f i:ℝ)) ⬝ᵥ z ≤ (q:ℝ) := by
  rw [B.withLevel_realEval,blockScalar_posSemidef,sub_nonneg]
end CurrentKS.RationalSDP

end OAI
