import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallDivisorTail

namespace OAI

/-! # Uniform truncation of the middle-divisor Fourier frequencies -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

 theorem quadratic_middle_frequency_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, ∀ X U V : ℝ, 0 < X → 0 < V → ∀ L : ℕ,
      ‖∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          quadraticLatticeOuter (𝓕 ψ) (X / d) L‖ ≤
        C * V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_tail_norm (𝓕 ψ) A
  refine ⟨C, hC, ?_⟩
  intro q X U V hX hV L
  let S := q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V)
  have hcard : (S.card : ℝ) ≤ V := by
    apply le_trans _ (quadratic_low_divisor_card q hV.le)
    exact_mod_cast Finset.card_le_card (show S ⊆ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V) from by
      intro d hd
      obtain ⟨hd, _, hbound⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨hd, hbound⟩)
  have hterm (d : ℕ) (hd : d ∈ S) :
      ‖(ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeOuter (𝓕 ψ) (X / d) L‖ ≤
        C * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := by
    obtain ⟨hd, _, hdV⟩ := Finset.mem_filter.mp hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hxd : 0 < X / d := div_pos hX hdR
    have ht := hc (X / d) hxd L
    have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxd]
    calc
      _ ≤ 1 * (X / d) * (C / ((X / d) ^ (A + 2) * ((L : ℝ) + 1) ^ A)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hmu hxd.le) ht (norm_nonneg _) (by positivity)
      _ = C * ((d : ℝ) / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := by
        rw [div_pow, div_pow]
        simp only [pow_add, pow_one, pow_two]
        field_simp
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ d ∈ S, ‖(ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeOuter (𝓕 ψ) (X / d) L‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ S, C * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (C * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by simp
    _ ≤ V * (C * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
