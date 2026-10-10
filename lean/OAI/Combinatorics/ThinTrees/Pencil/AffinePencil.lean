import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Grid

namespace OAI

/-! Affine pencil. -/

section

namespace AlgorithmicThinTrees.RationalForms
open Matrix Finset
open scoped BigOperators

abbrev Affine (d : ℕ) := ℚ × (Fin d → ℚ)

namespace Affine
variable {d : ℕ}

def cst (q : ℚ) : Affine d := (q,0)
def coord (i : Fin d) : Affine d := (0,Pi.single i 1)

noncomputable def real (z : Fin d → ℝ) (a : Affine d) : ℝ :=
  (a.1:ℝ)+∑i, (a.2 i:ℝ)*z i

@[simp] lemma real_cst (z : Fin d → ℝ) (q : ℚ) : real z (cst q)=(q:ℝ) := by
  simp [real,cst]
@[simp] lemma real_coord (z : Fin d → ℝ) (i : Fin d) : real z (coord i)=z i := by
  simp [real,coord,Pi.single_apply,apply_ite,ite_mul]
@[simp] lemma real_zero (z : Fin d → ℝ) : real z (0 : Affine d)=0 := by
  simp [real]
@[simp] lemma real_add (z : Fin d → ℝ) (a b : Affine d) : real z (a+b)=real z a+real z b := by
  simp [real,add_mul,sum_add_distrib]
  ring
@[simp] lemma real_sub (z : Fin d → ℝ) (a b : Affine d) : real z (a-b)=real z a-real z b := by
  simp [real,sub_mul,sum_sub_distrib]
  ring
@[simp] lemma real_smul (z : Fin d → ℝ) (q : ℚ) (a : Affine d) :
    real z (q • a)=(q:ℝ)*real z a := by
  simp [real,mul_add,mul_assoc,mul_sum]
@[simp] lemma real_sum {I : Type*} (s : Finset I) (f : I → Affine d) (z : Fin d → ℝ) :
    real z (∑i ∈ s,f i)=∑i ∈ s,real z (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih]

lemma ext_real {a b : Affine d} (h : ∀z : Fin d → ℝ,real z a=real z b) : a=b := by
  have hc : a.1=b.1 := by
    have hh := h 0
    simp only [real,Pi.zero_apply,mul_zero,sum_const_zero,add_zero] at hh
    exact_mod_cast hh
  apply Prod.ext hc
  funext i
  have hh := h (Pi.single i 1)
  simp only [real,hc,Pi.single_apply,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,
    ite_true,add_right_inj] at hh
  exact_mod_cast hh

end Affine

def pencil {d N : ℕ} (A : Matrix (Fin N) (Fin N) (Affine d)) (hA : A.IsSymm) :
    CurrentKS.RationalSDP.Pencil d N where
  constant i j := (A i j).1
  coeff k i j := (A i j).2 k
  symmetric_constant := IsSymm.ext fun i j => congrArg Prod.fst (hA.apply i j)
  symmetric_coeff k := IsSymm.ext fun i j => congrArg (fun a => a.2 k) (hA.apply i j)

lemma pencil_realEval {d N : ℕ} (A : Matrix (Fin N) (Fin N) (Affine d))
    (hA : A.IsSymm) (z : Fin d → ℝ) :
    (pencil A hA).realEval z=A.map (Affine.real z) := by
  ext i j
  simp only [CurrentKS.RationalSDP.Pencil.realEval,pencil,Matrix.add_apply,Matrix.map_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Affine.real]
  congr 1
  apply sum_congr rfl
  intro k _
  change z k * (((A i j).2 k) : ℝ) = (((A i j).2 k) : ℝ) * z k
  ring

lemma symmetric_of_real {I : Type*} {d : ℕ} (A : Matrix I I (Affine d))
    (h : ∀z, (A.map (Affine.real z)).IsSymm) : A.IsSymm :=
  IsSymm.ext fun i j => Affine.ext_real (fun z => (h z).apply i j)

lemma blockDiagonal_psd {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (M : J → Matrix I I ℝ) : (Matrix.blockDiagonal M).PosSemidef ↔ ∀j, (M j).PosSemidef := by
  constructor
  · intro h j
    convert h.submatrix (fun i : I => (i,j)) using 1
    ext i k
    simp [Matrix.blockDiagonal]
  · intro h
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · apply isHermitian_iff_isSymm.mpr
      apply IsSymm.ext
      intro i k
      simp only [Matrix.blockDiagonal,Matrix.of_apply]
      by_cases he : i.2=k.2
      · simp only [he,ite_true]
        exact (isHermitian_iff_isSymm.mp (h k.2).isHermitian).apply _ _
      · simp only [he,Ne.symm he,ite_false]
    · intro v
      have hn := sum_nonneg (s:=univ) (fun j _ => (h j).dotProduct_mulVec_nonneg (fun i => v (i,j)))
      change 0 ≤ ∑ j, ∑ i, v (i,j)*(∑ k, M j i k*v (k,j)) at hn
      rw [sum_comm] at hn
      simpa only [dotProduct,Matrix.mulVec,Matrix.blockDiagonal,Matrix.of_apply,Fintype.sum_prod_type,
        Pi.star_apply,star_trivial,ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true] using hn

lemma blockDiagonal_map {I J : Type*} [DecidableEq J] {d : ℕ}
    (M : J → Matrix I I (Affine d)) (z : Fin d → ℝ) :
    (Matrix.blockDiagonal M).map (Affine.real z)=Matrix.blockDiagonal (fun j => (M j).map (Affine.real z)) := by
  ext i j
  simp only [Matrix.blockDiagonal,Matrix.map_apply,Matrix.of_apply]
  split_ifs <;> simp

lemma diagonal_map {I : Type*} [DecidableEq I] {d : ℕ}
    (f : I → Affine d) (z : Fin d → ℝ) :
    (Matrix.diagonal f).map (Affine.real z)=Matrix.diagonal (fun i => Affine.real z (f i)) := by
  ext i j
  simp only [Matrix.diagonal,Matrix.map_apply,Matrix.of_apply]
  split_ifs <;> simp

lemma fromBlocks_map {I J : Type*} {d : ℕ}
    (A : Matrix I I (Affine d)) (B : Matrix J J (Affine d)) (z : Fin d → ℝ) :
    (Matrix.fromBlocks A 0 0 B).map (Affine.real z)=
      Matrix.fromBlocks (A.map (Affine.real z)) 0 0 (B.map (Affine.real z)) := by
  ext i j
  cases i <;> cases j <;> simp

lemma fromBlocks_psd {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℝ) (B : Matrix J J ℝ) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef ↔ A.PosSemidef ∧ B.PosSemidef := by
  constructor
  · intro h
    exact ⟨h.submatrix Sum.inl,h.submatrix Sum.inr⟩
  · rintro ⟨ha,hb⟩
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · exact Matrix.isHermitian_fromBlocks_iff.mpr ⟨ha.isHermitian,by simp,by simp,hb.isHermitian⟩
    · intro v
      simpa only [dotProduct,Fintype.sum_sum_type,Matrix.fromBlocks_mulVec,
        Matrix.zero_mulVec,add_zero,zero_add,Sum.elim_inl,Sum.elim_inr,
        Pi.star_apply,star_trivial,Function.comp_def] using
        add_nonneg (ha.dotProduct_mulVec_nonneg (v ∘ Sum.inl))
          (hb.dotProduct_mulVec_nonneg (v ∘ Sum.inr))

lemma submatrix_equiv_psd {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℝ) (e : J ≃ I) :
    (A.submatrix e e).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    have hh := h.submatrix e.symm
    have he : (A.submatrix e e).submatrix e.symm e.symm = A := by ext i j; simp
    rw [he] at hh
    exact hh
  · exact fun h => h.submatrix e

end AlgorithmicThinTrees.RationalForms
end

end OAI
