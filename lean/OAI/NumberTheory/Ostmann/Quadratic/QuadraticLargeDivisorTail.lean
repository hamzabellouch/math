import OAI.NumberTheory.Ostmann.Quadratic.QuadraticInverseSquareTail

namespace OAI

/-! # Uniformly summing the large-divisor physical tails -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

 theorem quadratic_large_divisor_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, ∀ X V : ℝ, 0 < X → 0 < V →
      ‖∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X)‖ ≤
        C * X * (X / V) ^ (A + 1) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_nonzero_lattice ψ A
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro q X V hX hV
  have hterm (d : ℕ) (hd : d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ))) :
      ‖(ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X)‖ ≤
        (C * X ^ (A + 2) / V ^ A) * (1 / (d : ℝ) ^ 2) := by
    obtain ⟨hd, hdV⟩ := Finset.mem_filter.mp hd
    have hdR : (0 : ℝ) < d := hV.trans hdV
    have hdx : 0 < (d : ℝ) / X := div_pos hdR hX
    have hs : Summable (fun n : ℤ => ‖ψ ((n : ℝ) * (d / X))‖) := by
      simpa only [div_inv_eq_mul] using quadratic_scaled_summable ψ (inv_pos.mpr hdx)
    have hs' : Summable (fun n : ℤ => ‖if n = 0 then 0 else ψ ((n : ℝ) * (d / X))‖) := by
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
      intro n
      split_ifs <;> simp
    have ht : ‖quadraticLatticeTail ψ (d / X)‖ ≤ C / ((d : ℝ) / X) ^ (A + 2) := by
      apply (norm_tsum_le_tsum_norm hs').trans
      simpa only [apply_ite, norm_zero] using hc (d / X) hdx
    have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [norm_mul]
    calc
      _ ≤ 1 * (C / ((d : ℝ) / X) ^ (A + 2)) := by gcongr
      _ = (C * X ^ (A + 2) / (d : ℝ) ^ A) * (1 / (d : ℝ) ^ 2) := by
        rw [div_pow, pow_add]
        field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_left (by positivity) (pow_pos hV A)
          (pow_le_pow_left₀ hV.le hdV.le A)
  calc
    _ ≤ ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        ‖(ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (C * X ^ (A + 2) / V ^ A) * (1 / (d : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (C * X ^ (A + 2) / V ^ A) *
        ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), 1 / (d : ℝ) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (C * X ^ (A + 2) / V ^ A) * (2 / V) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact quadratic_inverse_square_tail _ hV (fun d hd => (Finset.mem_filter.mp hd).2)
    _ = _ := by
      rw [div_pow]
      simp only [pow_add, pow_one, pow_two]
      field_simp

end Ostmann

end OAI
