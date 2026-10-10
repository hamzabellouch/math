import OAI.NumberTheory.TotientAsymptotic.CollisionCount
import OAI.NumberTheory.TotientAsymptotic.Renewal

namespace OAI

/-! Absorbing prime-occurrence allocation costs into the collision saving. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma allocation_cost_le_exp (n b h d k : ℕ) (hn : n ≤ h) (hb : b ≤ h)
    (β : ℝ) (hd : (d : ℝ) ≤ β) (hk : (k : ℝ) ≤ β) :
    (n+1 : ℝ)^(d+k)*(b+1 : ℝ)^d ≤
      Real.exp (3*β*Real.log (h+1)) := by
  have hlog : 0 ≤ Real.log (h+1 : ℝ) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) h
    linarith)
  calc
    _ ≤ (h+1 : ℝ)^(d+k)*(h+1 : ℝ)^d := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1) _
      · exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hb 1) _
      · positivity
      · positivity
    _ = (h+1 : ℝ)^(2*d+k) := by rw [← pow_add]; congr 1; omega
    _ = Real.exp ((2*d+k : ℕ)*Real.log (h+1 : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ hlog
      push_cast
      linarith

lemma allocation_cost_absorbed {h : ℝ} (hh : 3 ≤ h) {B : ℝ} (hB : 0 ≤ B) :
    3*(B/h^8)*Real.log (h+1) ≤ B/(4*h^4) := by
  have h0 : 0 < h := by linarith
  have hlog : Real.log (h+1) ≤ h := by
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < h+1)
  have hcube : 27 ≤ h^3 := by nlinarith [sq_nonneg (h-3)]
  have hh4 : 12*h ≤ h^4 := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 4*h^4)).mpr
  have he : (3*(B/h^8)*Real.log (h+1))*(4*h^4) =
      (12*B*Real.log (h+1)*h^4)/h^8 := by ring
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < h^8)).mpr
  have hpow : h^8 = h^4*h^4 := by ring
  rw [hpow]
  have hbase : 12*B*Real.log (h+1) ≤ B*h^4 := by
    have hb := mul_le_mul_of_nonneg_left (show 12*Real.log (h+1) ≤ h^4 by linarith) hB
    nlinarith
  have hb := mul_le_mul_of_nonneg_right hbase (pow_nonneg h0.le 4)
  nlinarith

end TotientAsymptotic

end

end OAI
