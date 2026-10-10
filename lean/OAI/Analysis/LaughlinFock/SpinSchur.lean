import Mathlib
import OAI.Analysis.LaughlinFock.Averaging
import OAI.Analysis.LaughlinFock.LadderCalculus

namespace OAI

/-! Spin Schur. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory

section Derivative
open scoped Matrix.Norms.Operator

 
theorem matrix_commutes_generator_of_flow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A X : Matrix ι ι ℂ)
    (h : ∀ t : ℝ, A * exp ((t : ℂ) • X) = exp ((t : ℂ) • X) * A) :
    A * X = X * A := by
  have hc (t : ℝ) : (t : ℂ) • X = t • X := by
    exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) t X).symm
  simp_rw [hc] at h
  have he : (fun t : ℝ => A * exp (t • X)) = (fun t => exp (t • X) * A) := funext h
  have hd := hasDerivAt_exp_smul_const X (0 : ℝ)
  have h₁ : HasDerivAt (fun t : ℝ => A * exp (t • X))
      (A * (exp ((0 : ℝ) • X) * X)) 0 := hd.const_mul A
  have h₂ := hd.mul_const A
  rw [he] at h₁
  simpa only [zero_smul, exp_zero, Matrix.one_mul] using! h₁.unique h₂

 

theorem rotationAverage_commutes_generator {J σ : Type*} {I : J → Type*}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j)
    (j : J) (M : Matrix (I j) (I j) ℂ) (s : σ) :
    rotationAverage X hX j M * X s j = X s j * rotationAverage X hX j M := by
  apply matrix_commutes_generator_of_flow
  intro t
  exact rotationAverage_commutes X hX j M
    ⟨rotationFlow X hX s t, rotationFlow_mem_group X hX s t⟩

end Derivative

 
def spinLowerMatrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := fun i j =>
  if i.val = j.val+1 then (spinStep n i.val : ℂ) else 0

 
def spinWeightMatrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  Matrix.diagonal (fun i => (n : ℂ) - 2 * (i.val : ℂ))

 
def spinGenerator (n : ℕ) (s : Fin 3) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  if s = 0 then spinLowerMatrix n - (spinLowerMatrix n)ᴴ
  else if s = 1 then Complex.I • (spinLowerMatrix n + (spinLowerMatrix n)ᴴ)
  else Complex.I • spinWeightMatrix n

theorem spinWeightMatrix_adjoint (n : ℕ) : (spinWeightMatrix n)ᴴ = spinWeightMatrix n := by
  simp [spinWeightMatrix, Matrix.diagonal_conjTranspose]

theorem spinGenerator_skew (n : ℕ) (s : Fin 3) :
    (spinGenerator n s)ᴴ = -spinGenerator n s := by
  fin_cases s <;> simp [spinGenerator, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, spinWeightMatrix_adjoint, sub_eq_add_neg, add_comm]

 

theorem spinGenerator_intertwiner {n m : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (m+1)) ℂ)
    (hA : ∀ s, spinGenerator n s * A = A * spinGenerator m s) :
    spinLowerMatrix n * A = A * spinLowerMatrix m ∧
    (spinLowerMatrix n)ᴴ * A = A * (spinLowerMatrix m)ᴴ ∧
    spinWeightMatrix n * A = A * spinWeightMatrix m := by
  have h₀ : (spinLowerMatrix n - (spinLowerMatrix n)ᴴ) * A =
      A * (spinLowerMatrix m - (spinLowerMatrix m)ᴴ) := by
    simpa [spinGenerator] using hA 0
  have h₁ : (Complex.I • (spinLowerMatrix n + (spinLowerMatrix n)ᴴ)) * A =
      A * (Complex.I • (spinLowerMatrix m + (spinLowerMatrix m)ᴴ)) := by
    simpa [spinGenerator] using hA 1
  have h₂ : (Complex.I • spinWeightMatrix n) * A =
      A * (Complex.I • spinWeightMatrix m) := by
    simpa [spinGenerator] using hA 2
  simp only [Matrix.smul_mul, Matrix.mul_smul] at h₁ h₂
  have hi : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have he₁ := smul_right_injective _ hi h₁
  have he₂ := smul_right_injective _ hi h₂
  refine ⟨?_, ?_, he₂⟩
  · ext i j
    have he := congrArg (fun M => M i j) h₀
    have hf := congrArg (fun M => M i j) he₁
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_apply, Matrix.add_apply] at he hf
    linear_combination (he + hf) / 2
  · ext i j
    have he := congrArg (fun M => M i j) h₀
    have hf := congrArg (fun M => M i j) he₁
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_apply, Matrix.add_apply] at he hf
    linear_combination (hf - he) / 2

 

theorem mul_spinLower_succ {κ : Type*} {n : ℕ}
    (A : Matrix κ (Fin (n+1)) ℂ) (i : κ) (j : ℕ) (hj : j < n) :
    (A * spinLowerMatrix n) i ⟨j, by omega⟩ =
      A i ⟨j+1, by omega⟩ * (spinStep n (j+1) : ℂ) := by
  classical
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (⟨j+1, by omega⟩ : Fin (n+1))]
  · simp [spinLowerMatrix]
  · intro b _ hb
    have hne : b.val ≠ j+1 := fun he => hb (Fin.ext he)
    simp [spinLowerMatrix, hne]
  · simp

 
theorem mul_spinRaise_zero {κ : Type*} {n : ℕ}
    (A : Matrix κ (Fin (n+1)) ℂ) (i : κ) :
    (A * (spinLowerMatrix n)ᴴ) i 0 = 0 := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, spinLowerMatrix]

 
theorem spinRaise_mul_pred {κ : Type*} {n : ℕ}
    (A : Matrix (Fin (n+1)) κ ℂ) (i : Fin (n+1)) (hi : 0 < i.val) (j : κ) :
    ((spinLowerMatrix n)ᴴ * A) ⟨i.val-1, by omega⟩ j =
      (spinStep n i.val : ℂ) * A i j := by
  classical
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.conjTranspose_apply, spinLowerMatrix, Nat.sub_add_cancel hi]
  · intro b _ hb
    have hne : b.val ≠ i.val := fun he => hb (Fin.ext he)
    simp [Matrix.conjTranspose_apply, spinLowerMatrix, Nat.sub_add_cancel hi, hne]
  · simp

 

theorem spin_intertwiner_zero_of_first_column {n m : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (m+1)) ℂ)
    (hL : spinLowerMatrix n * A = A * spinLowerMatrix m)
    (h₀ : ∀ i, A i 0 = 0) : A = 0 := by
  have hc (k : ℕ) (hk : k ≤ m) : ∀ i, A i ⟨k, by omega⟩ = 0 := by
    induction k with
    | zero => exact h₀
    | succ k ih =>
      have ih' := ih (by omega)
      intro i
      have he := congrArg (fun R => R i (⟨k, by omega⟩ : Fin (m+1))) hL
      rw [mul_spinLower_succ A i k (by omega)] at he
      have hz : (spinLowerMatrix n * A) i ⟨k, by omega⟩ = 0 := by
        simp only [Matrix.mul_apply, ih', mul_zero, Finset.sum_const_zero]
      rw [hz] at he
      have hs : (spinStep m (k+1) : ℂ) ≠ 0 := by
        exact_mod_cast (spinStep_pos (by omega) hk).ne'
      exact (mul_eq_zero.mp he.symm).resolve_right hs
  ext i j
  exact hc j.val (by omega) i

theorem spin_intertwiner_first_column {n m : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (m+1)) ℂ)
    (hR : (spinLowerMatrix n)ᴴ * A = A * (spinLowerMatrix m)ᴴ)
    (i : Fin (n+1)) (hi : 0 < i.val) : A i 0 = 0 := by
  have he := congrArg (fun R => R (⟨i.val-1, by omega⟩ : Fin (n+1)) 0) hR
  rw [spinRaise_mul_pred A i hi, mul_spinRaise_zero] at he
  have hs : (spinStep n i.val : ℂ) ≠ 0 := by
    exact_mod_cast (spinStep_pos hi (by omega)).ne'
  exact (mul_eq_zero.mp he).resolve_left hs

 

theorem spin_intertwiner_scalar {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hA : ∀ s, spinGenerator n s * A = A * spinGenerator n s) :
    A = A 0 0 • 1 := by
  obtain ⟨hL,hR,_⟩ := spinGenerator_intertwiner A hA
  have he : A - A 0 0 • 1 = 0 := by
    apply spin_intertwiner_zero_of_first_column
    · simp [Matrix.mul_sub, Matrix.sub_mul, hL]
    · intro i
      by_cases hi : i = 0
      · subst i; simp
      · have hip : 0 < i.val := by
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          omega
        simp [Matrix.sub_apply, Matrix.smul_apply, hi,
          spin_intertwiner_first_column A hR i hip]
  exact sub_eq_zero.mp he

 

theorem spin_intertwiner_zero_of_ne {n m : ℕ} (hnm : n ≠ m)
    (A : Matrix (Fin (n+1)) (Fin (m+1)) ℂ)
    (hA : ∀ s, spinGenerator n s * A = A * spinGenerator m s) : A = 0 := by
  obtain ⟨hL,hR,hW⟩ := spinGenerator_intertwiner A hA
  apply spin_intertwiner_zero_of_first_column A hL
  intro i
  by_cases hi : i = 0
  · subst i
    have he := congrArg (fun R => R 0 0) hW
    simp [spinWeightMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    have hz : ((n : ℂ)-(m : ℂ)) * A 0 0 = 0 := by linear_combination he
    have hn : (n : ℂ)-(m : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
    exact (mul_eq_zero.mp hz).resolve_left hn
  · have hip : 0 < i.val := by
      have : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    exact spin_intertwiner_first_column A hR i hip

theorem spin_intertwiner_trace_scalar {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hA : ∀ s, spinGenerator n s * A = A * spinGenerator n s) :
    A = (A.trace / (n+1 : ℂ)) • 1 := by
  have he := spin_intertwiner_scalar A hA
  have ht := congrArg Matrix.trace he
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hz : A 0 0 = A.trace / (n+1 : ℂ) := by
    apply (eq_div_iff hn).mpr
    simpa [Matrix.trace_smul, Matrix.trace_one] using ht.symm
  rwa [hz] at he

end LaughlinFock
end

end OAI
