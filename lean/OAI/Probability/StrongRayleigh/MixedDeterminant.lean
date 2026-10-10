import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

noncomputable section
open scoped ComplexConjugate ComplexOrder Topology

namespace Problem336AdditiveD139

open Matrix

theorem det_fromBlocks_skew_nonneg_of_posDef
    {m : Type u_1} {n : Type u_2} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.PosDef) (hD : D.PosSemidef) :
    0 ≤ (Matrix.fromBlocks A B (-Bᴴ) D).det := by
  let := hA.isUnit.invertible
  rw [Matrix.det_fromBlocks₁₁]
  have hInv : (⅟ A : Matrix m m ℂ) = A⁻¹ := by
    exact Matrix.invOf_eq_nonsing_inv A
  rw [hInv, Matrix.neg_mul, Matrix.neg_mul, sub_neg_eq_add]
  exact mul_nonneg hA.posSemidef.det_nonneg
    (hD.add (hA.posSemidef.inv.conjTranspose_mul_mul_same B)).det_nonneg

theorem det_fromBlocks_skew_nonneg
    {m : Type u_3} {n : Type u_4} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    0 ≤ (Matrix.fromBlocks A B (-Bᴴ) D).det := by
  have hc : Continuous (fun t : ℝ =>
      (Matrix.fromBlocks (A + t • (1 : Matrix m m ℂ)) B (-Bᴴ) D).det) := by
    fun_prop
  have ht : Filter.Tendsto (fun t : ℝ =>
      (Matrix.fromBlocks (A + t • (1 : Matrix m m ℂ)) B (-Bᴴ) D).det)
      (𝓝[>] (0 : ℝ)) (𝓝 (Matrix.fromBlocks A B (-Bᴴ) D).det) := by
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply det_fromBlocks_skew_nonneg_of_posDef _ _ _ _ hD
  exact Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul ht)

def mixedRowMatrix {F : Type u_5} [DecidableEq F]
    (K : Matrix F F ℂ) (x : F → Bool) : Matrix F F ℂ :=
  fun i j => if x i = true then K i j else (1 - K) i j

theorem mixedRowMatrix_det_nonneg
    {F : Type u_6} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) (x : F → Bool)
    (hK : K.PosSemidef) (hIK : (1 - K).PosSemidef) :
    0 ≤ (mixedRowMatrix K x).det := by
  let e := Equiv.sumCompl (fun i : F => x i = true)
  let A := K.submatrix (fun i : {i // x i = true} => i.1) (fun i : {i // x i = true} => i.1)
  let B := K.submatrix (fun i : {i // x i = true} => i.1)
    (fun i : {i // ¬ x i = true} => i.1)
  let D := (1 - K).submatrix (fun i : {i // ¬ x i = true} => i.1) (fun i : {i // ¬ x i = true} => i.1)
  have he : (mixedRowMatrix K x).submatrix e e =
      Matrix.fromBlocks A B (-Bᴴ) D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [mixedRowMatrix, e, A, Matrix.submatrix, i.property]
    · simp [mixedRowMatrix, e, B, Matrix.submatrix, i.property]
    · simp [mixedRowMatrix, e, B, Matrix.submatrix, i.property,
        Matrix.one_apply, hK.isHermitian.apply]
    · simp [mixedRowMatrix, e, D, Matrix.submatrix, i.property, Matrix.one_apply, Subtype.ext_iff]
  rw [← Matrix.det_submatrix_equiv_self e (mixedRowMatrix K x), he]
  exact det_fromBlocks_skew_nonneg A B D (hK.submatrix _) (hIK.submatrix _)

theorem mixedRowMatrix_det_re_nonneg
    {F : Type u_7} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) (x : F → Bool)
    (hK : K.PosSemidef) (hIK : (1 - K).PosSemidef) :
    0 ≤ (mixedRowMatrix K x).det.re :=
  (Complex.nonneg_iff.mp (mixedRowMatrix_det_nonneg K x hK hIK)).1

theorem mixedRowMatrix_det_im
    {F : Type u_8} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) (x : F → Bool)
    (hK : K.PosSemidef) (hIK : (1 - K).PosSemidef) :
    (mixedRowMatrix K x).det.im = 0 :=
  (Complex.nonneg_iff.mp (mixedRowMatrix_det_nonneg K x hK hIK)).2.symm

end Problem336AdditiveD139

end

end OAI
