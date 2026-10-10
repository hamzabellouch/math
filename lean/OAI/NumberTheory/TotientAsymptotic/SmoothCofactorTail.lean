import OAI.NumberTheory.TotientAsymptotic.SmoothCofactorMoment

namespace OAI

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The exponential tail needed for the actual smooth-cofactor truncation. -/
theorem smooth_cofactor_rankin {N : ℕ} (hN : 2 ≤ N) (Z : ℝ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N ∧ Z < Real.log n) :
    (∑ n ∈ Q, (n.totient : ℝ)⁻¹) ≤
      Real.exp (-Z/(4*Real.log N))*(primeEulerProduct N)^4 := by
  let σ := 1/(4*Real.log N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  calc
    _ ≤ Real.exp (-σ*Z)*∑ n ∈ Q, (n : ℝ)^σ/(n.totient : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ)<n := by exact_mod_cast (hQ n hn).1
      have hφ : 0 < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (hQ n hn).1
      have hm : 1 ≤ Real.exp (-σ*Z)*(n : ℝ)^σ := by
        rw [Real.rpow_def_of_pos hn0,← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by nlinarith [(hQ n hn).2.2])
      have hh := mul_le_mul_of_nonneg_right hm (inv_pos.mpr hφ).le
      simpa only [one_mul,div_eq_mul_inv,mul_assoc] using hh
    _ ≤ Real.exp (-σ*Z)*(primeEulerProduct N)^4 :=
      mul_le_mul_of_nonneg_left (smooth_cofactor_power_mass hN Q (fun n hn =>
        ⟨(hQ n hn).1,(hQ n hn).2.1⟩)) (Real.exp_pos _).le
    _ = _ := by congr 2; dsimp [σ]; ring

end TotientAsymptotic

end

end OAI
