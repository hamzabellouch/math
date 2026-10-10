import Mathlib

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.AntiConcentration
noncomputable section

def centralProbability (n : ℕ) : ℝ := (n.centralBinom : ℝ) / 4^n

theorem centralProbability_nonneg (n : ℕ) : 0 ≤ centralProbability n := by
  unfold centralProbability
  positivity

theorem centralProbability_step (n : ℕ) :
    centralProbability (n+1) = centralProbability n * ((2*(n:ℝ)+1)/(2*(n:ℝ)+2)) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : 2*(n : ℝ)+2 ≠ 0 := by positivity
  have h4 : (4 : ℝ)^n ≠ 0 := by positivity
  have hrec := congrArg (fun k : ℕ => (k : ℝ)) (Nat.succ_mul_centralBinom_succ n)
  push_cast at hrec
  have hc : ((n+1).centralBinom : ℝ) = 2*(2*(n:ℝ)+1)*(n.centralBinom : ℝ)/((n:ℝ)+1) := by
    apply (eq_div_iff hn).mpr
    nlinarith [hrec]
  unfold centralProbability
  rw [hc, pow_succ]
  field_simp
  ; ring

theorem centralProbability_sq (n : ℕ) :
    centralProbability n ^ 2 * ((n : ℝ)+1) ≤ 1 := by
  induction n with
  | zero => norm_num [centralProbability]
  | succ n ih =>
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hden : 0 < (2*(n : ℝ)+2)^2 := by positivity
      have hstep : ((2*(n : ℝ)+1)/(2*(n : ℝ)+2))^2 * ((n : ℝ)+2) ≤ (n : ℝ)+1 := by
        rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith
      rw [centralProbability_step]
      push_cast
      calc
        _ = centralProbability n ^2 *
            ((((2*(n:ℝ)+1)/(2*(n:ℝ)+2))^2) * ((n:ℝ)+2)) := by ring
        _ ≤ centralProbability n ^2 * ((n:ℝ)+1) :=
          mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
        _ ≤ 1 := ih

theorem centralProbability_le (n : ℕ) :
    centralProbability n ≤ 1 / Real.sqrt ((n : ℝ)+1) := by
  have hs : 0 < Real.sqrt ((n : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  apply (le_div_iff₀ hs).mpr
  have hsq : (centralProbability n * Real.sqrt ((n : ℝ)+1))^2 ≤ (1:ℝ)^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    simpa only [one_pow] using centralProbability_sq n
  exact (sq_le_sq₀ (mul_nonneg (centralProbability_nonneg n) hs.le) zero_le_one).mp hsq

theorem centralProbability_lt (n : ℕ) (hn : 0 < n) :
    centralProbability n < Real.sqrt 2 / Real.sqrt (2*(n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hs2 : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hstrict : 1 / Real.sqrt ((n : ℝ)+1) < 1 / Real.sqrt (n : ℝ) := by
    exact one_div_lt_one_div_of_lt hnS (Real.sqrt_lt_sqrt hnR.le (by linarith))
  have heq : 1 / Real.sqrt (n : ℝ) = Real.sqrt 2 / Real.sqrt (2*(n : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  exact lt_of_le_of_lt (centralProbability_le n) (hstrict.trans_eq heq)

theorem sign_atom_le (n v : ℕ) :
    ((2*n).choose v : ℝ) / 2^(2*n) ≤ centralProbability n := by
  have hb : (2 : ℝ)^(2*n) = (4 : ℝ)^n := by rw [pow_mul]; norm_num
  rw [hb]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.choose_le_centralBinom v n)) (by positivity)

end
end VertexCover.AntiConcentration


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
