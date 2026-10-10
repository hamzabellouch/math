import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology
namespace Ostmann.Conclusion

def diagonalExponent (Bs BD Bz C : ℝ) (k : ℕ) (L : ℝ) (j : ℕ) : ℝ :=
  -stepGap BD Bz k L j + (2 : ℝ)^j *
    (initialGap Bs k L + (Real.log (bulkScale k) +
      (1/4 : ℝ)*Real.log ((2 : ℝ)^j) + C)*(bulkSize k L : ℝ))

theorem diagonalExponent_eq (Bs BD Bz C : ℝ) (k : ℕ) (L : ℝ) (j : ℕ) :
    diagonalExponent Bs BD Bz C k L j =
      (Bs-BD+(9-Bz)*Real.log (bulkScale k)-(3/20 : ℝ)*Real.log ((2 : ℝ)^j)+C)*
        (2 : ℝ)^j*(bulkSize k L : ℝ) := by
  unfold diagonalExponent stepGap initialGap
  ring

theorem bulkScale_one_le {k : ℕ} (hk : 1 ≤ k) : 1 ≤ bulkScale k := by
  exact one_le_pow₀ (by exact_mod_cast hk)

theorem diagonalExponent_reserve {Bs BD Bz C B : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hBz : 9 ≤ Bz) (hBD : Bs+2*B+C+6 ≤ BD) (L : ℝ) (j : ℕ) :
    diagonalExponent Bs BD Bz C k L j ≤ -(2*B+6)*(2 : ℝ)^j*(bulkSize k L : ℝ) := by
  have hz := Real.log_nonneg (bulkScale_one_le hk)
  have hr := Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) :
    1 ≤ (2 : ℝ)^j)
  have hterm : (9-Bz)*Real.log (bulkScale k) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hz
  have hrate : Bs-BD+(9-Bz)*Real.log (bulkScale k)-
      (3/20 : ℝ)*Real.log ((2 : ℝ)^j)+C ≤ -(2*B+6) := by linarith
  rw [diagonalExponent_eq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrate (by positivity))
    (by positivity)

theorem exp_pair_le {u v t : ℝ} (hu : u ≤ t-Real.log 2) (hv : v ≤ t-Real.log 2) :
    Real.exp u + Real.exp v ≤ Real.exp t := by
  have h := add_le_add (Real.exp_le_exp.mpr hu) (Real.exp_le_exp.mpr hv)
  calc
    _ ≤ Real.exp (t-Real.log 2)+Real.exp (t-Real.log 2) := h
    _ = Real.exp t := by rw [Real.exp_sub,Real.exp_log (by norm_num : (0 : ℝ)<2)]; ring

theorem diagonal_total_reserve {Bs BD Bz C B L D e ω : ℝ} {k j : ℕ}
    (hk : 1 ≤ k) (hBz : 9 ≤ Bz) (hBD : Bs+2*B+C+6 ≤ BD)
    (he : e ≤ (2 : ℝ)^j*(bulkSize k L : ℝ))
    (hω : (2*B+5)*(2 : ℝ)^j*(bulkSize k L : ℝ) ≤ ω)
    (hm : Real.log 2 ≤ (2 : ℝ)^j*(bulkSize k L : ℝ))
    (hD : D ≤ Real.exp (diagonalExponent Bs BD Bz C k L j+e)+Real.exp (-ω)) :
    D ≤ Real.exp (-(2*B+4)*(2 : ℝ)^j*(bulkSize k L : ℝ)) := by
  have hdiag := diagonalExponent_reserve hk hBz hBD L j
  refine hD.trans (exp_pair_le ?_ ?_) <;> nlinarith

theorem giant_cost_reserve {k : ℕ} (hk : 2 ≤ k) (c : ℝ → ℝ)
    (hc : ∀ᶠ L : ℝ in atTop, c L ≤ (91/100 : ℝ)*L) :
    ∀ᶠ L : ℝ in atTop, c L+Real.log 2 ≤ (bulkSize k L : ℝ) := by
  have hz : (2 : ℝ) ≤ bulkScale k := by
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    unfold bulkScale
    nlinarith [sq_nonneg ((k : ℝ)^2-2)]
  filter_upwards [hc,eventually_ge_atTop (Real.log 2+2),eventually_ge_atTop (0 : ℝ)]
    with L hcL hL hL0
  have h := (bulkSize_bounds k hL0).1
  have hzL := mul_le_mul_of_nonneg_right hz hL0
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

end Ostmann.Conclusion

end

end OAI
