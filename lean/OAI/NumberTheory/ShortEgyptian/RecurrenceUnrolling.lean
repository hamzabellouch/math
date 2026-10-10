import OAI.NumberTheory.ShortEgyptian.MomentRecurrence

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma nat_rpow_le_self (k : ℕ) {α : ℝ} (ha : 0 < α) (ha' : α ≤ 1) : (k:ℝ)^α ≤ k := by
  by_cases hk : k = 0
  · simp only [hk,Nat.cast_zero,Real.zero_rpow ha.ne',le_refl]
  · exact Real.rpow_le_self_of_one_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk) ha'

lemma backwards_recurrence_bound (f : ℕ → ℝ) (d : ℕ) (α c γ b : ℝ)
    (ha : 0 < α) (ha' : α ≤ 1) (hg : 0 ≤ γ) (hb : 0 ≤ b)
    (hfix : c+γ*α=γ) (hf : ∀ j, 0 ≤ f j) (hend : f d=0)
    (hrec : ∀ j, j < d → f j ≤ Real.exp (-b)+Real.exp c*(f (j+1))^α) :
    f 0 ≤ (d:ℝ)*Real.exp (γ-b*α^d) := by
  have hind (k : ℕ) (hk : k ≤ d) : f (d-k) ≤ (k:ℝ)*Real.exp (γ-b*α^k) := by
    induction k with
    | zero => simpa only [Nat.sub_zero,Nat.cast_zero,zero_mul,hend] using (le_refl (0:ℝ))
    | succ k ih =>
      have hk' : k ≤ d := by omega
      have ih := ih hk'
      have hj : d-(k+1) < d := by omega
      have heq : d-(k+1)+1=d-k := by omega
      have hstep := hrec (d-(k+1)) hj
      rw [heq] at hstep
      have hp := Real.rpow_le_rpow (hf (d-k)) ih ha.le
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.exp_nonneg _),←Real.exp_mul] at hp
      have he : Real.exp c*((k:ℝ)^α*Real.exp ((γ-b*α^k)*α)) =
          (k:ℝ)^α*Real.exp (γ-b*α^(k+1)) := by
        rw [←mul_assoc,mul_comm (Real.exp c),mul_assoc,←Real.exp_add]
        congr 2
        rw [pow_succ]
        nlinarith [hfix]
      have hpow : α^(k+1) ≤ 1 := pow_le_one₀ ha.le ha'
      have heps : Real.exp (-b) ≤ Real.exp (γ-b*α^(k+1)) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hpow hb])
      calc
        _ ≤ Real.exp (-b)+Real.exp c*(f (d-k))^α := hstep
        _ ≤ Real.exp (-b)+Real.exp c*((k:ℝ)^α*Real.exp ((γ-b*α^k)*α)) := by gcongr
        _ = Real.exp (-b)+(k:ℝ)^α*Real.exp (γ-b*α^(k+1)) := by rw [he]
        _ ≤ Real.exp (γ-b*α^(k+1))+(k:ℝ)*Real.exp (γ-b*α^(k+1)) :=
          add_le_add heps (mul_le_mul_of_nonneg_right (nat_rpow_le_self k ha ha') (Real.exp_nonneg _))
        _ = _ := by push_cast; ring
  simpa only [Nat.sub_self] using hind d le_rfl

lemma log_one_sub_inverse_lower (r : ℝ) (hr : 2 ≤ r) :
    -(2/r) ≤ Real.log (1-1/r) := by
  have hrp : 0 < r := by linarith
  have hrm : 0 < r-1 := by linarith
  have ha : 0 < 1-1/r := by rw [sub_pos,div_lt_one hrp]; linarith
  have he : (1-1/r)⁻¹=r/(r-1) := by field_simp
  have hd : r/(r-1) ≤ 1+2/r := by
    apply (div_le_iff₀ hrm).mpr
    apply (mul_le_mul_iff_of_pos_right hrp).mp
    field_simp
    nlinarith
  have hl := Real.one_sub_inv_le_log_of_pos ha
  rw [he] at hl
  linarith

end ShortEgyptian

end OAI
