import OAI.MeasureTheory.Falconer.Estimates.ScalarPrefixEntropy

namespace OAI

/-! Comparing the porous projection gain with the exact discarded
 branching. This is the numerical endgame of the scalar dichotomy. -/
namespace Falconer

 theorem scalar_bunch_gain_log {R S W : ℕ} {E D : ℝ} (hD : 0 < D)
    (h : (2:ℝ)^R*Real.exp E ≤ D*(2:ℝ)^(R+S+W)) :
    E ≤ Real.log D+((S:ℝ)+(W:ℝ))*Real.log 2 := by
  have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^R*Real.exp E) h
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero E),Real.log_pow,Real.log_exp,
    Real.log_mul hD.ne' (by positivity),Real.log_pow] at hh
  simp only [Nat.cast_add] at hh
  nlinarith

 theorem scalar_bunch_net_gain {R S W P T lo : ℕ} {D : ℝ} (hD : 0 < D)
    (hlo : lo ≤ T) (hshort : 10*lo ≤ T)
    (hS : (S:ℝ) ≤ (P:ℝ)*((T-lo:ℕ):ℝ)/50)
    (hW : (W:ℝ) ≤ 2*(P:ℝ)*(lo:ℝ))
    (h : (2:ℝ)^R*Real.exp ((1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) ≤
      D*(2:ℝ)^(R+S+W)) :
    (1/5:ℝ)*(P:ℝ)*(T:ℝ)*Real.log 2 ≤ Real.log D := by
  have hlog := scalar_bunch_gain_log hD h
  have hbase : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hcovered : ((T-lo:ℕ):ℝ) = (T:ℝ)-(lo:ℝ) := Nat.cast_sub hlo
  have hloR : 10*(lo:ℝ) ≤ (T:ℝ) := by exact_mod_cast hshort
  have hbudget : (S:ℝ)+(W:ℝ) ≤
      (P:ℝ)*((T-lo:ℕ):ℝ)/50+2*(P:ℝ)*(lo:ℝ) := add_le_add hS hW
  have hb := mul_le_mul_of_nonneg_right hbudget hbase
  have hm := mul_le_mul_of_nonneg_left hloR (mul_nonneg (Nat.cast_nonneg P) hbase)
  rw [hcovered] at hlog hb
  nlinarith

end Falconer

end OAI
