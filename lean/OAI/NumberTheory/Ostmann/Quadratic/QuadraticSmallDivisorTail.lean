import OAI.NumberTheory.Ostmann.Quadratic.QuadraticHybridPoisson

namespace OAI

/-! # Uniformly summing the small-divisor Fourier tails -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

theorem quadratic_low_divisor_card (q : ℕ) {U : ℝ} (hU : 0 ≤ U) :
    (((q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U)).card : ℝ)) ≤ U := by
  have hc : (q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U)).card ≤ ⌊U⌋₊ := by
    calc
      _ ≤ (Finset.Icc 1 ⌊U⌋₊).card := by
        apply Finset.card_le_card
        intro d hd
        obtain ⟨hd, hbound⟩ := Finset.mem_filter.mp hd
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_floor hbound⟩
      _ = _ := by simp
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hU)

 theorem quadratic_small_divisor_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, ∀ X U : ℝ, 0 < X → 0 < U →
      ‖∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U),
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          quadraticLatticeTail (𝓕 ψ) (X / d)‖ ≤ C * U * (U / X) ^ (A + 1) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_nonzero_lattice (𝓕 ψ) A
  refine ⟨C, hC, ?_⟩
  intro q X U hX hU
  have hterm (d : ℕ) (hd : d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U)) :
      ‖(ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeTail (𝓕 ψ) (X / d)‖ ≤ C * (U / X) ^ (A + 1) := by
    obtain ⟨hd, hdU⟩ := Finset.mem_filter.mp hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hxd : 0 < X / d := div_pos hX hdR
    have hs : Summable (fun n : ℤ => ‖(𝓕 ψ) ((n : ℝ) * (X / d))‖) := by
      simpa only [div_inv_eq_mul] using quadratic_scaled_summable (𝓕 ψ) (inv_pos.mpr hxd)
    have hs' : Summable (fun n : ℤ => ‖if n = 0 then 0 else (𝓕 ψ) ((n : ℝ) * (X / d))‖) := by
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
      intro n
      split_ifs <;> simp
    have ht : ‖quadraticLatticeTail (𝓕 ψ) (X / d)‖ ≤ C / (X / d) ^ (A + 2) := by
      apply (norm_tsum_le_tsum_norm hs').trans
      simpa only [apply_ite, norm_zero] using hc (X / d) hxd
    have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxd]
    calc
      _ ≤ 1 * (X / d) * (C / (X / d) ^ (A + 2)) := by gcongr
      _ = C * ((d : ℝ) / X) ^ (A + 1) := by
        rw [div_pow, div_pow]
        simp only [pow_add, pow_one, pow_two]
        field_simp
      _ ≤ C * (U / X) ^ (A + 1) := by gcongr
  calc
    _ ≤ ∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U),
        ‖(ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          quadraticLatticeTail (𝓕 ψ) (X / d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U), C * (U / X) ^ (A + 1) :=
      Finset.sum_le_sum hterm
    _ = (((q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U)).card : ℝ)) *
        (C * (U / X) ^ (A + 1)) := by simp
    _ ≤ U * (C * (U / X) ^ (A + 1)) :=
      mul_le_mul_of_nonneg_right (quadratic_low_divisor_card q hU.le) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
