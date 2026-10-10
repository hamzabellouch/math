import OAI.NumberTheory.JointDickman.Counting.HyperbolaBlockBound

namespace OAI

/-! # A uniform budget for the rational hyperbola blocks -/
namespace JointDickman

lemma rectangle_budget_uniform (Q U q : ℕ) (N Z L : ℝ)
    (hN : 0 < N) (hZ : 0 < Z) (hq : 0 < q) (_hL : 0 ≤ L)
    (hlog : Real.log Q ≤ L) (hQU : (Q:ℝ)*U ≤ 2*N)
    (hU : (U:ℝ) ≤ N/Z) (hQ : (Q:ℝ) ≤ 2*N/Z) :
    (Q:ℝ)*Real.log Q*(U:ℝ)^2 + Q*(U:ℝ)^2*Q*(1+Real.log q)/q +
      Q*U*Q + Q*U*q*(1+Real.log Q) ≤
    N^2*(2*L/Z+4*(1+Real.log q)/q+4/Z+2*q*(1+L)/N) := by
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogQ : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  have hN0 := hN.le
  have hZ0 := hZ.le
  have hquad : ((Q:ℝ)*U)^2 ≤ (2*N)^2 :=
    pow_le_pow_left₀ (by positivity) hQU 2
  calc
    _ = ((Q:ℝ)*U)*U*Real.log Q + ((Q:ℝ)*U)^2*(1+Real.log q)/q +
        ((Q:ℝ)*U)*Q + ((Q:ℝ)*U)*q*(1+Real.log Q) := by ring
    _ ≤ (2*N)*(N/Z)*L+(2*N)^2*(1+Real.log q)/q+
        (2*N)*(2*N/Z)+(2*N)*q*(1+L) := by
      gcongr
    _ = _ := by field_simp; ring

lemma rounding_budget_uniform (U H Q : ℕ) (N Z : ℝ)
    (hH : 0 < H) (_hN : 0 ≤ N) (_hZ : 0 < Z)
    (hQU : (Q:ℝ)*U ≤ 2*N) (hQ : (Q:ℝ) ≤ 2*N/Z) :
    ((U/H+1:ℕ):ℝ)*Real.log 4*Q ≤
      N*Real.log 4*(2/(H:ℝ)+2/Z) := by
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hwidth := quotient_cell_width U H hH
  calc
    _ ≤ ((U:ℝ)/H+1)*Real.log 4*Q := by gcongr
    _ = Real.log 4*(((Q:ℝ)*U)/H+Q) := by ring
    _ ≤ Real.log 4*((2*N)/(H:ℝ)+2*N/Z) := by gcongr
    _ = _ := by ring

end JointDickman

end OAI
