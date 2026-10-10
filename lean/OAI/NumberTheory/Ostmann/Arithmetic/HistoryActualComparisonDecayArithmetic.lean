import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedComparisonAbsorptionBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryActualComparisonDecayArithmetic
open HistorySelectedComparisonAbsorption

theorem nat_mul_exp_reserve_le (n : ℕ) (x m : ℝ) (hm : 1 ≤ m) :
    (n:ℝ)*Real.exp (x-(n:ℝ)*m) ≤ Real.exp x := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    using finite_sum_exp_reserve_le
      (fun _ : Fin n => Real.exp (x-(n:ℝ)*m)) x m hm (fun _ => by simp only [Fintype.card_fin]; exact le_rfl)

theorem five_stage_exp_le {F H m : ℝ} (hm : 1 ≤ m)
    (z₀ z₁ z₂ z₃ z₄ z₅ : ℂ)
    (h₀₁ : ‖z₀-z₁‖ ≤ Real.exp (-F-(H+5)*m))
    (h₁₂ : ‖z₁-z₂‖ ≤ Real.exp (-F-(H+5)*m))
    (h₂₃ : ‖z₂-z₃‖ ≤ Real.exp (-F-(H+5)*m))
    (h₃₄ : ‖z₃-z₄‖ ≤ Real.exp (-F-(H+5)*m))
    (h₄₅ : ‖z₄-z₅‖ ≤ Real.exp (-F-(H+5)*m)) :
    ‖z₀-z₅‖ ≤ Real.exp (-F-H*m) := by
  have htri : ‖z₀-z₅‖ ≤ 5*Real.exp (-F-(H+5)*m) := by
    have h₀ := dist_triangle z₀ z₁ z₅
    have h₁ := dist_triangle z₁ z₂ z₅
    have h₂ := dist_triangle z₂ z₃ z₅
    have h₃ := dist_triangle z₃ z₄ z₅
    simp only [dist_eq_norm] at h₀ h₁ h₂ h₃
    linarith
  have hcap := nat_mul_exp_reserve_le 5 (-F-H*m) m hm
  have heq : -F-H*m-(5:ℝ)*m = -F-(H+5)*m := by ring
  rw [Nat.cast_ofNat, heq] at hcap
  exact htri.trans hcap

theorem five_stage_bulk_exp_le {H m : ℝ} (hm : 1 ≤ m)
    (z₀ z₁ z₂ z₃ z₄ z₅ : ℂ)
    (h₀₁ : ‖z₀-z₁‖ ≤ Real.exp (-(H+5)*m))
    (h₁₂ : ‖z₁-z₂‖ ≤ Real.exp (-(H+5)*m))
    (h₂₃ : ‖z₂-z₃‖ ≤ Real.exp (-(H+5)*m))
    (h₃₄ : ‖z₃-z₄‖ ≤ Real.exp (-(H+5)*m))
    (h₄₅ : ‖z₄-z₅‖ ≤ Real.exp (-(H+5)*m)) :
    ‖z₀-z₅‖ ≤ Real.exp (-H*m) := by
  simpa only [neg_zero,zero_sub,neg_mul] using
    five_stage_exp_le (F:=0) hm z₀ z₁ z₂ z₃ z₄ z₅
      (by simpa only [neg_zero,zero_sub,neg_mul] using h₀₁)
      (by simpa only [neg_zero,zero_sub,neg_mul] using h₁₂)
      (by simpa only [neg_zero,zero_sub,neg_mul] using h₂₃)
      (by simpa only [neg_zero,zero_sub,neg_mul] using h₃₄)
      (by simpa only [neg_zero,zero_sub,neg_mul] using h₄₅)

theorem five_stage_exp_le_of_steps {F H m : ℝ} (hm : 1 ≤ m) (z : Fin 6→ℂ)
    (hz : ∀i : Fin 5,‖z i.castSucc-z i.succ‖ ≤ Real.exp (-F-(H+5)*m)) :
    ‖z 0-z 5‖ ≤ Real.exp (-F-H*m) :=
  five_stage_exp_le hm (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)
    (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)

theorem two_terms_exp_67_65_le (k : ℕ) {F m a b : ℝ} (hm : 1 ≤ m)
    (ha : a ≤ Real.exp (-(F+67*(2:ℝ)^k*m)))
    (hb : b ≤ Real.exp (-(F+67*(2:ℝ)^k*m))) :
    a+b ≤ Real.exp (-(F+65*(2:ℝ)^k*m)) := by
  have hr : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hs : 1 ≤ (2:ℝ)^k*m := by nlinarith
  have hcap := nat_mul_exp_reserve_le 2 (-(F+65*(2:ℝ)^k*m)) ((2:ℝ)^k*m) hs
  have heq : -(F+65*(2:ℝ)^k*m)-(2:ℝ)*((2:ℝ)^k*m) =
      -(F+67*(2:ℝ)^k*m) := by ring
  rw [Nat.cast_ofNat,heq] at hcap
  exact (show a+b ≤ 2*Real.exp (-(F+67*(2:ℝ)^k*m)) by linarith).trans hcap

theorem two_norms_exp_67_65_le (k : ℕ) {F m : ℝ} (hm : 1 ≤ m) (z w : ℂ)
    (hz : ‖z‖ ≤ Real.exp (-(F+67*(2:ℝ)^k*m)))
    (hw : ‖w‖ ≤ Real.exp (-(F+67*(2:ℝ)^k*m))) :
    ‖z‖+‖w‖ ≤ Real.exp (-(F+65*(2:ℝ)^k*m)) :=
  two_terms_exp_67_65_le k hm hz hw

theorem norm_add_exp_67_65_le (k : ℕ) {F m : ℝ} (hm : 1 ≤ m) (z w : ℂ)
    (hz : ‖z‖ ≤ Real.exp (-(F+67*(2:ℝ)^k*m)))
    (hw : ‖w‖ ≤ Real.exp (-(F+67*(2:ℝ)^k*m))) :
    ‖z+w‖ ≤ Real.exp (-(F+65*(2:ℝ)^k*m)) :=
  (norm_add_le z w).trans (two_norms_exp_67_65_le k hm z w hz hw)

end Ostmann.Arithmetic.HistoryActualComparisonDecayArithmetic

end

end OAI
