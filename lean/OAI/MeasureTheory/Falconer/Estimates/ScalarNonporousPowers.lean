import OAI.MeasureTheory.Falconer.Estimates.ScalarForkSumset

namespace OAI

/-! Scale arithmetic for a subsequence of nonporous dyadic blocks. -/
namespace Falconer.Regularization

 theorem scalar_dyadic_shift (b n C : ℕ) (h : b ≤ n+C) :
    (1/2:ℝ)^n ≤ (2:ℝ)^C*(1/2:ℝ)^b := by
  have hh : (1/2:ℝ)^(n+C) ≤ (1/2:ℝ)^b :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have he : (1/2:ℝ)^(n+C)*(2:ℝ)^C = (1/2:ℝ)^n := by
    rw [pow_add,mul_assoc,← mul_pow]
    norm_num
  have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) C)
  rw [he] at hm
  simpa only [mul_comm] using hm

 theorem scalar_dyadic_contract {W : ℝ} (hW : 0 ≤ W) (B x y : ℕ)
    (hgap : x+B ≤ y) (hc : (1/2:ℝ)^B*W ≤ 1) :
    (1/2:ℝ)^y*W ≤ (1/2:ℝ)^x := by
  have hp : (1/2:ℝ)^y ≤ (1/2:ℝ)^(x+B) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hgap
  calc
    _ ≤ (1/2:ℝ)^(x+B)*W := mul_le_mul_of_nonneg_right hp hW
    _ = (1/2:ℝ)^x*((1/2:ℝ)^B*W) := by rw [pow_add,mul_assoc]
    _ ≤ (1/2:ℝ)^x*1 := mul_le_mul_of_nonneg_left hc (pow_nonneg (by norm_num) x)
    _ = _ := mul_one _

noncomputable def scalarSelectedScale (B : ℕ) (g : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then (1/2:ℝ)^(B*g 0) else (1/2:ℝ)^(B*(g (i-1)+1))

 theorem scalarSelectedScale_succ (B : ℕ) (g : ℕ → ℕ) (i : ℕ) :
    scalarSelectedScale B g (i+1) = (1/2:ℝ)^(B*(g i+1)) := by
  simp [scalarSelectedScale]

 theorem scalarSelectedScale_pos (B : ℕ) (g : ℕ → ℕ) (i : ℕ) :
    0 < scalarSelectedScale B g i := by
  unfold scalarSelectedScale
  split_ifs <;> positivity

 theorem scalarSelectedScale_contract {W : ℝ} (hW : 0 ≤ W) (B t : ℕ) (g : ℕ → ℕ)
    (hg : ∀ i < t, g i < g (i+1)) (hc : (1/2:ℝ)^B*W ≤ 1) :
    ∀ i < t, scalarSelectedScale B g (i+1)*W ≤ scalarSelectedScale B g i := by
  intro i hi
  rw [scalarSelectedScale_succ]
  by_cases hi0 : i = 0
  · subst i
    rw [scalarSelectedScale,ite_eq_left rfl]
    apply scalar_dyadic_contract hW B _ _ _ hc
    simp only [Nat.mul_add,Nat.mul_one]
    exact le_rfl
  · rw [scalarSelectedScale,ite_eq_right hi0]
    apply scalar_dyadic_contract hW B _ _ _ hc
    have hprev := hg (i-1) (by omega)
    have hie : i-1+1 = i := by omega
    rw [hie] at hprev
    have hm := Nat.mul_le_mul_left B (show g (i-1)+1+1 ≤ g i+1 by omega)
    simpa only [Nat.mul_add,Nat.mul_one] using hm

end Falconer.Regularization

end OAI
