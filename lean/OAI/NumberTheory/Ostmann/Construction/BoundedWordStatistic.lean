import OAI.NumberTheory.Ostmann.Construction.PositiveWordStatistic

namespace OAI

/-! # The initial positive statistic with its actual finite physical bounds -/

namespace Ostmann
open scoped BigOperators SchwartzMap

/-- The inverse giant transform need not have norm at most one. Only a finite
bound is needed to sum its Schwartz-weighted physical statistic. -/
theorem wordStatisticTerm_summable_of_bounded {m : ℕ}
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (CG : ℝ) (CR : Fin m → ℝ)
    (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hG : ∀ a, ‖G a‖ ≤ CG) (hR : ∀ i a, ‖R i a‖ ≤ CR i) :
    Summable (wordStatisticTerm ψ X G R) := by
  have hsum : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded (hsum.mul_right (CG ^ 2 * ∏ i, CR i ^ 2))
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (wordStatisticTerm_nonneg ψ X G R hψ a)]
  have hg : ‖G a‖ ^ 2 ≤ CG ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hG a) 2
  have hr : (∏ i, ‖R i a‖ ^ 2) ≤ ∏ i, CR i ^ 2 :=
    Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hR i a) 2)
  calc
    wordStatisticTerm ψ X G R a ≤
        ‖ψ ((a : ℝ) / X)‖ * (CG ^ 2 * ∏ i, CR i ^ 2) := by
      unfold wordStatisticTerm
      rw [← mul_assoc]
      exact mul_le_mul (mul_le_mul (Complex.re_le_norm _) hg
        (sq_nonneg _) (norm_nonneg _)) hr (by positivity) (by positivity)
    _ = _ := rfl

/-- Cauchy--Schwarz converts a positive empirical mean into the squared norm
needed for the original statistic, without pointwise positivity of the giant. -/
theorem endpoint_mean_sq_le {ι : Type*} (E : Finset ι) (G : ι → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E, (G a).re) :
    (E.card : ℝ) * δ ^ 2 ≤ ∑ a ∈ E, ‖G a‖ ^ 2 := by
  by_cases hE : E.card = 0
  · have he : E = ∅ := Finset.card_eq_zero.mp hE
    simp only [he, Finset.card_empty, Nat.cast_zero, zero_mul, Finset.sum_empty, le_refl]
  have hc : (0 : ℝ) < E.card := by exact_mod_cast Nat.pos_of_ne_zero hE
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq E (fun _ => (1 : ℝ)) (fun a => (G a).re)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hre : (∑ a ∈ E, (G a).re ^ 2) ≤ ∑ a ∈ E, ‖G a‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    simpa only [Complex.normSq_eq_norm_sq, pow_two] using Complex.re_sq_le_normSq (G a)
  have hlow : ((E.card : ℝ) * δ) ^ 2 ≤ (∑ a ∈ E, (G a).re) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hc.le hδ) hmean 2
  have hupper := hcs.trans (mul_le_mul_of_nonneg_left hre hc.le)
  nlinarith

/-- The selected endpoint mean feeds the whole statistic. No pointwise bound
of one and no pointwise lower bound on the giant function is imposed. -/
theorem wordStatistic_lower_of_endpoint_mean {m : ℕ}
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (E : Finset ℤ)
    (CG : ℝ) (CR : Fin m → ℝ)
    (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hG : ∀ a, ‖G a‖ ≤ CG) (hR : ∀ i a, ‖R i a‖ ≤ CR i)
    (c δ γ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E, (G a).re)
    (hγE : ∀ a ∈ E, ∀ i, γ ≤ ‖R i a‖) :
    (E.card : ℝ) * (c * δ ^ 2 * γ ^ (2 * m)) ≤
      ∑' a : ℤ, wordStatisticTerm ψ X G R a := by
  have hm := endpoint_mean_sq_le E G δ hδ hmean
  have hfinite : c * γ ^ (2 * m) * (∑ a ∈ E, ‖G a‖ ^ 2) ≤
      ∑ a ∈ E, wordStatisticTerm ψ X G R a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hr : γ ^ (2 * m) ≤ ∏ i, ‖R i a‖ ^ 2 := by
      rw [pow_mul]
      calc
        (γ ^ 2) ^ m = ∏ _i : Fin m, γ ^ 2 := by simp
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
          (fun i _ => pow_le_pow_left₀ hγ (hγE a ha i) 2)
    unfold wordStatisticTerm
    calc
      c * γ ^ (2 * m) * ‖G a‖ ^ 2 = c * ‖G a‖ ^ 2 * γ ^ (2 * m) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hcE a ha) (sq_nonneg _)) hr
        (by positivity) (mul_nonneg (hψ _) (sq_nonneg _))
  calc
    _ = c * γ ^ (2 * m) * ((E.card : ℝ) * δ ^ 2) := by ring
    _ ≤ c * γ ^ (2 * m) * (∑ a ∈ E, ‖G a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ ∑ a ∈ E, wordStatisticTerm ψ X G R a := hfinite
    _ ≤ _ := (wordStatisticTerm_summable_of_bounded ψ X hX G R CG CR hψ hG hR).sum_le_tsum E
      (fun a _ => wordStatisticTerm_nonneg ψ X G R hψ a)

end Ostmann

end OAI
