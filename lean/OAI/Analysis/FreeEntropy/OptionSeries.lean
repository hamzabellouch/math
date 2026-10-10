import OAI.Analysis.FreeEntropy.SpectralMatrixProducer

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β : Type} [DecidableEq α] [Fintype α]

def ignoreLetter (f : Series α) : Series (Option α) := fun w => f (w.filterMap id)

omit [DecidableEq α] [Fintype α] in
theorem deriv_ignore_none [DecidableEq α] [Fintype α] (f : Series α) : deriv none (ignoreLetter f) = ignoreLetter f := rfl

omit [DecidableEq α] [Fintype α] in
theorem deriv_ignore_some [DecidableEq α] [Fintype α] (f : Series α) (a : α) :
    deriv (some a) (ignoreLetter f) = ignoreLetter (deriv a f) := rfl
 theorem ignoreLetter_norm_sq (f : Series α) (n : ℕ) :
    degreeNorm (ignoreLetter f) n^2 =
      ∑ k ∈ range (n+1), (n.choose k : ℝ) * degreeNorm f k^2 := by
  induction n generalizing f with
  | zero => simp [degreeNorm_nil, ignoreLetter]
  | succ n ih =>
    rw [degreeNorm_succ_sq, Fintype.sum_option, deriv_ignore_none, ih]
    simp only [deriv_ignore_some, ih]
    rw [sum_comm]
    simp only [← mul_sum, ← degreeNorm_succ_sq]
    exact (Finset.sum_choose_succ_mul (fun k _ => degreeNorm f k^2) n).symm
 theorem ignoreLetter_norm_le {f : Series α} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ n, degreeNorm f n ≤ A^n) (n : ℕ) :
    degreeNorm (ignoreLetter f) n ≤ (A+1)^n := by
  apply (sq_le_sq₀ (degreeNorm_nonneg _ _) (pow_nonneg (by linarith) _)).mp
  rw [ignoreLetter_norm_sq]
  calc
    _ ≤ ∑ k ∈ range (n+1), (n.choose k : ℝ) * (A^k)^2 := by
      apply sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (degreeNorm_nonneg _ _) (hf k) 2) (by positivity)
    _ = (A^2+1)^n := by
      rw [add_pow]
      apply sum_congr rfl
      intro k hk
      rw [one_pow, mul_one, ← pow_mul, ← pow_mul, Nat.mul_comm k 2, mul_comm]
    _ ≤ ((A+1)^2)^n := pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]

 def vectorMap (e : α ≃ β) (n : ℕ) : List.Vector α n ≃ List.Vector β n where
  toFun w := ⟨w.val.map e, by simp [w.prop]⟩
  invFun w := ⟨w.val.map e.symm, by simp [w.prop]⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp

omit [DecidableEq α] in
theorem degreeNorm_equiv [DecidableEq α] [Fintype β] (e : α ≃ β) (f : Series β) (n : ℕ) :
    degreeNorm (fun w => f (w.map e)) n = degreeNorm f n := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _)).mp
  rw [degreeNorm_sq, degreeNorm_sq]
  exact (vectorMap e n).sum_comp (fun w : List.Vector β n => ‖f w.val‖^2)

def optionFin (p : ℕ) : Option (Fin p) ≃ Fin (p+1) where
  toFun := fun a => match a with | none => Fin.last p | some i => i.castSucc
  invFun := Fin.lastCases none some
  left_inv a := by cases a <;> simp
  right_inv a := by induction a using Fin.lastCases <;> simp
@[simp] theorem optionFin_none (p : ℕ) : optionFin p none = Fin.last p := rfl
@[simp] theorem optionFin_some (p : ℕ) (i : Fin p) : optionFin p (some i) = i.castSucc := rfl

end FiniteEntropySeparation.FreeSeries

end

end OAI
