import Mathlib
import OAI.Analysis.LaughlinFock.WedgeLie

namespace OAI

/-! Coupled Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem spinLower_sum (n : ℕ) (i : Fin (n+1)) (f : ℕ → ℂ) :
    (∑ a : Fin (n+1), spinLowerMatrix n i a * f a.val) =
      (spinStep n i.val : ℂ) * f (i.val-1) := by
  classical
  by_cases hi : i.val=0
  · simp [spinLowerMatrix, hi]
  · have hip : 0 < i.val := by omega
    rw [Finset.sum_eq_single (⟨i.val-1, by omega⟩ : Fin (n+1))]
    · simp [spinLowerMatrix, Nat.sub_add_cancel hip]
    · intro b _ hb
      have hn : i.val ≠ b.val+1 := by
        intro he; apply hb; apply Fin.ext; dsimp only; omega
      simp [spinLowerMatrix, hn]
    · simp

theorem spinRaise_sum (n : ℕ) (i : Fin (n+1)) (f : ℕ → ℂ) :
    (∑ a : Fin (n+1), (spinLowerMatrix n)ᴴ i a * f a.val) =
      (spinStep n (i.val+1) : ℂ) * f (i.val+1) := by
  classical
  by_cases hi : i.val < n
  · rw [Finset.sum_eq_single (⟨i.val+1, by omega⟩ : Fin (n+1))]
    · simp [Matrix.conjTranspose_apply, spinLowerMatrix]
    · intro b _ hb
      have hn : b.val ≠ i.val+1 := fun he => hb (Fin.ext he)
      simp [Matrix.conjTranspose_apply, spinLowerMatrix, hn]
    · simp
  · have he : i.val=n := by omega
    have hz (b : Fin (n+1)) : b.val ≠ i.val+1 := by omega
    simp only [Matrix.conjTranspose_apply, spinLowerMatrix, ite_eq_right (hz _)]
    simp [he]

theorem sum_spinLower (n : ℕ) (j : Fin (n+1)) (f : ℕ → ℂ) :
    (∑ a : Fin (n+1), f a.val * spinLowerMatrix n a j) =
      (spinStep n (j.val+1) : ℂ) * f (j.val+1) := by
  have he (a : Fin (n+1)) : spinLowerMatrix n a j = (spinLowerMatrix n)ᴴ j a := by
    simp only [spinLowerMatrix, Matrix.conjTranspose_apply]
    split_ifs <;> simp
  simpa only [he, mul_comm] using spinRaise_sum n j f

theorem sum_spinRaise (n : ℕ) (j : Fin (n+1)) (f : ℕ → ℂ) :
    (∑ a : Fin (n+1), f a.val * (spinLowerMatrix n)ᴴ a j) =
      (spinStep n j.val : ℂ) * f (j.val-1) := by
  have he (a : Fin (n+1)) : (spinLowerMatrix n)ᴴ a j = spinLowerMatrix n j a := by
    simp only [spinLowerMatrix, Matrix.conjTranspose_apply]
    split_ifs <;> simp
  simpa only [he, mul_comm] using spinLower_sum n j f

theorem tensorSum_mul_apply {ι κ β : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (C : Matrix (ι × κ) β ℂ)
    (i : ι) (j : κ) (k : β) :
    (tensorSum X Y * C) (i,j) k =
      (∑ a, X i a * C (a,j) k) + ∑ b, Y j b * C (i,b) k := by
  classical
  simp only [Matrix.mul_apply, tensorSum_apply, add_mul, Finset.sum_add_distrib,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  rw [Finset.sum_comm]
  simp

 

def coupledSpinMatrix (n m z : ℕ) :
    Matrix (Fin (n+1) × Fin (m+1)) (Fin (n+m-2*z+1)) ℂ := fun ij k =>
  (coupledVector n m z k.val ij.1.val ij.2.val : ℂ)

theorem tensorLower_coupled_apply (n m z : ℕ) (i : Fin (n+1)) (j : Fin (m+1))
    (k : Fin (n+m-2*z+1)) :
    (tensorSum (spinLowerMatrix n) (spinLowerMatrix m) * coupledSpinMatrix n m z) (i,j) k =
      (gridLower n m (coupledVector n m z k.val) i.val j.val : ℂ) := by
  rw [tensorSum_mul_apply]
  change (∑ a : Fin (n+1), spinLowerMatrix n i a *
      (coupledVector n m z k.val a.val j.val : ℂ)) +
    (∑ a : Fin (m+1), spinLowerMatrix m j a *
      (coupledVector n m z k.val i.val a.val : ℂ)) = _
  rw [spinLower_sum n i (fun a => (coupledVector n m z k.val a j.val : ℂ)),
    spinLower_sum m j (fun a => (coupledVector n m z k.val i.val a : ℂ))]
  by_cases hi : i.val=0 <;> by_cases hj : j.val=0 <;>
    simp [gridLower, hi, hj]

theorem tensorRaise_coupled_apply (n m z : ℕ) (i : Fin (n+1)) (j : Fin (m+1))
    (k : Fin (n+m-2*z+1)) :
    (tensorSum (spinLowerMatrix n)ᴴ (spinLowerMatrix m)ᴴ * coupledSpinMatrix n m z) (i,j) k =
      (gridRaise n m (coupledVector n m z k.val) i.val j.val : ℂ) := by
  rw [tensorSum_mul_apply]
  change (∑ a : Fin (n+1), (spinLowerMatrix n)ᴴ i a *
      (coupledVector n m z k.val a.val j.val : ℂ)) +
    (∑ a : Fin (m+1), (spinLowerMatrix m)ᴴ j a *
      (coupledVector n m z k.val i.val a.val : ℂ)) = _
  rw [spinRaise_sum n i (fun a => (coupledVector n m z k.val a j.val : ℂ)),
    spinRaise_sum m j (fun a => (coupledVector n m z k.val i.val a : ℂ))]
  simp [gridRaise]

theorem coupledSpinMatrix_lower {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    tensorSum (spinLowerMatrix n) (spinLowerMatrix m) * coupledSpinMatrix n m z =
      coupledSpinMatrix n m z * spinLowerMatrix (n+m-2*z) := by
  ext ⟨i,j⟩ k
  rw [tensorLower_coupled_apply, coupledVector_lower_all hn hm]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Matrix.mul_apply,
    coupledSpinMatrix]
  exact (sum_spinLower (n+m-2*z) k (fun t => (coupledVector n m z t i.val j.val : ℂ))).symm

theorem coupledSpinMatrix_raise {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    tensorSum (spinLowerMatrix n)ᴴ (spinLowerMatrix m)ᴴ * coupledSpinMatrix n m z =
      coupledSpinMatrix n m z * (spinLowerMatrix (n+m-2*z))ᴴ := by
  ext ⟨i,j⟩ k
  rw [tensorRaise_coupled_apply, coupledVector_raise_all hn hm]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Matrix.mul_apply,
    coupledSpinMatrix]
  exact (sum_spinRaise (n+m-2*z) k (fun t => (coupledVector n m z t i.val j.val : ℂ))).symm

theorem coupledSpinMatrix_weight {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    tensorSum (spinWeightMatrix n) (spinWeightMatrix m) * coupledSpinMatrix n m z =
      coupledSpinMatrix n m z * spinWeightMatrix (n+m-2*z) := by
  ext ⟨i,j⟩ k
  rw [tensorSum_mul_apply]
  simp only [spinWeightMatrix, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.mul_diagonal, coupledSpinMatrix]
  by_cases hl : i.val+j.val=z+k.val
  · have he : (n : ℂ) - 2*i.val + ((m : ℂ)-2*j.val) =
        ((n+m-2*z : ℕ) : ℂ) - 2*k.val := by
      push_cast [Nat.cast_sub (show 2*z ≤ n+m by omega)]
      have hh : (i.val : ℂ)+j.val = z+k.val := by exact_mod_cast hl
      linear_combination -2 * hh
    rw [← add_mul, he, mul_comm]
  · simp [coupledVector, hl]

theorem tensorSum_add {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X X' : Matrix ι ι ℂ) (Y Y' : Matrix κ κ ℂ) :
    tensorSum (X+X') (Y+Y') = tensorSum X Y + tensorSum X' Y' := by
  ext i j
  simp only [tensorSum_apply, Matrix.add_apply]
  split_ifs <;> ring

theorem tensorSum_smul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (c : ℂ) :
    tensorSum (c•X) (c•Y) = c • tensorSum X Y := by
  ext i j
  simp only [tensorSum_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem tensorSum_sub {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X X' : Matrix ι ι ℂ) (Y Y' : Matrix κ κ ℂ) :
    tensorSum (X-X') (Y-Y') = tensorSum X Y - tensorSum X' Y' := by
  ext i j
  simp only [tensorSum_apply, Matrix.sub_apply]
  split_ifs <;> ring

 
theorem coupledSpinMatrix_intertwines {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (s : Fin 3) :
    tensorSum (spinGenerator n s) (spinGenerator m s) * coupledSpinMatrix n m z =
      coupledSpinMatrix n m z * spinGenerator (n+m-2*z) s := by
  fin_cases s <;> simp only [spinGenerator, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  · rw [tensorSum_sub, Matrix.sub_mul, coupledSpinMatrix_lower hn hm,
      coupledSpinMatrix_raise hn hm, Matrix.mul_sub]
  · rw [tensorSum_smul, tensorSum_add, Matrix.smul_mul, Matrix.add_mul,
      coupledSpinMatrix_lower hn hm, coupledSpinMatrix_raise hn hm,
      Matrix.mul_smul, Matrix.mul_add]
  · rw [tensorSum_smul, Matrix.smul_mul, coupledSpinMatrix_weight hn hm, Matrix.mul_smul]

end LaughlinFock
end

end OAI
