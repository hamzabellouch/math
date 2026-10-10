import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Laughlin
noncomputable section
open scoped BigOperators

def fallingRatio (Q z : ℕ) : ℝ :=
  (Q.descFactorial z : ℝ) / ((2*Q-2).descFactorial z : ℝ)

theorem fallingRatio_le_geometric {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    fallingRatio Q z ≤ (2/3 : ℝ)^z := by
  have hr (i : ℕ) (hi : i ∈ Finset.range z) :
      ((Q-i : ℕ) : ℝ) / ((2*Q-2-i : ℕ) : ℝ) ≤ (2/3 : ℝ) := by
    have hiQ : i ≤ Q := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hz
    have hid : i ≤ 2*Q-2 := by omega
    have h2 : 2 ≤ 2*Q := by omega
    rw [Nat.cast_sub hiQ, Nat.cast_sub hid, Nat.cast_sub h2]
    push_cast
    have hQr : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hir : (i : ℝ) ≤ Q := by exact_mod_cast hiQ
    have hden : 0 < 2*(Q : ℝ)-2-i := by linarith
    apply (div_le_iff₀ hden).mpr
    linarith [Nat.cast_nonneg (α := ℝ) i]
  calc
    fallingRatio Q z = ∏ i ∈ Finset.range z,
        (((Q-i : ℕ) : ℝ) / ((2*Q-2-i : ℕ) : ℝ)) := by
      simp [fallingRatio, Nat.descFactorial_eq_prod_range, Nat.cast_prod,
        Finset.prod_div_distrib]
    _ ≤ ∏ _i ∈ Finset.range z, (2/3 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        positivity
      · exact hr
    _ = _ := by simp [div_pow]

def gramEigenvalueFormula (Q z : ℕ) : ℝ :=
  (-1 : ℝ)^z * fallingRatio Q z *
    (3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ))

theorem tail_bracket_bounds {Q z : ℕ} (hQ : 4 ≤ Q) (hz₀ : 16 ≤ z) (hz : z ≤ Q) :
    0 ≤ 3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ) ∧
      3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ) ≤ 3*(z : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hzr : (16 : ℝ) ≤ z := by exact_mod_cast hz₀
  have hzQr : (z : ℝ) ≤ Q := by exact_mod_cast hz
  have hd : (z : ℝ)*((z : ℝ)+1)/(Q : ℝ) ≤ (z : ℝ)+1 := by
    apply (div_le_iff₀ hQr).mpr
    nlinarith
  have hn : 0 ≤ (z : ℝ)*((z : ℝ)+1)/(Q : ℝ) := by positivity
  constructor <;> linarith

theorem gramEigenvalueFormula_abs_le {Q z : ℕ}
    (hQ : 4 ≤ Q) (hz₀ : 16 ≤ z) (hz : z ≤ Q) :
    |gramEigenvalueFormula Q z| ≤ (2/3 : ℝ)^z * (3*(z : ℝ)) := by
  have hratio : 0 ≤ fallingRatio Q z := by unfold fallingRatio; positivity
  have hb := tail_bracket_bounds hQ hz₀ hz
  unfold gramEigenvalueFormula
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hratio, abs_of_nonneg hb.1]
  exact mul_le_mul (fallingRatio_le_geometric hQ hz) hb.2 hb.1 (by positivity)

def tailWeight (Q z : ℕ) : ℝ :=
  ((3*(Q : ℝ)-1-2*(z : ℝ))/(2*(Q : ℝ)-1)) *
    |gramEigenvalueFormula Q z| * ((z : ℝ)+1)

theorem tailWeight_le {Q z : ℕ} (hQ : 4 ≤ Q) (hz₀ : 16 ≤ z) (hz : z ≤ Q) :
    tailWeight Q z ≤ 6*(z : ℝ)*((z : ℝ)+1)*(2/3 : ℝ)^z := by
  have hQr : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hdim : (3*(Q : ℝ)-1-2*(z : ℝ))/(2*(Q : ℝ)-1) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 2*(Q : ℝ)-1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) z]
  unfold tailWeight
  calc
    _ ≤ (2*((2/3 : ℝ)^z * (3*(z : ℝ)))) * ((z : ℝ)+1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hdim (gramEigenvalueFormula_abs_le hQ hz₀ hz) (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end
end Laughlin

end OAI
