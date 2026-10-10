import OAI.Probability.ContinuumTransition.FreeFamily

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

lemma freeFamily_integral (t d L : ℝ) (ι : Type) [Fintype ι] :
    familyIntegral (freeFamily t d) (cube L) ι =
      volume.real ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ {x | FreeConfig t x})*
        (Real.exp d)^Fintype.card ι := by
  have he : freeFamily t d ι = {x : ι → Space | FreeConfig t x}.indicator
      (fun _ => Real.exp (d*Fintype.card ι)) := by
    funext x
    simp only [freeFamily, indicator_apply, mem_ofPred_eq]
  rw [familyIntegral, he, setIntegral_indicator (measurableSet_freeConfig t), setIntegral_const,
    smul_eq_mul, mul_comm d, Real.exp_nat_mul]

lemma power_trunc_bound {w : ℝ} (hw : 0 ≤ w) {j k : ℕ} (hjk : j ≤ 3*k) :
    w^j ≤ (max 1 w)^ (3*k) := by
  exact (pow_le_pow_left₀ hw (le_max_right 1 w) j).trans
    (pow_le_pow_right₀ (le_max_left 1 w) hjk)

theorem free_grand_upper {t : ℝ} (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (d L : ℝ) :
    grandIntegral (freeFamily t d) (cube L) ≤
      (∑ k ∈ Finset.range (packingNumber L+1),
        ((volume.real (cube L))*Real.exp d*
          (max 1 (volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t)))*Real.exp d))^3)^k /
            (k.factorial : ℝ))*Real.exp (packingNumber L) := by
  let V := volume.real (cube L)
  let z := Real.exp d
  let w := volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t)))
  let M := packingNumber L
  let D := max 1 (w*z)
  let a : ℕ → ℝ := fun k => if k ≤ M then (V*z*D^3)^k/(k.factorial : ℝ) else 0
  let b : ℕ → ℝ := fun j => (M : ℝ)^j/(j.factorial : ℝ)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hz : 0 ≤ z := (Real.exp_pos _).le
  have hw : 0 ≤ w := ENNReal.toReal_nonneg
  have hD : 1 ≤ D := le_max_left _ _
  have ha : Summable a := summable_of_ne_finset_zero (s := Finset.range (M+1)) (by
    intro k hk
    have hh : ¬k ≤ M := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    simp only [a, ite_eq_right hh])
  have hb : HasSum b (Real.exp (M : ℝ)) := by
    simpa only [b, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (M : ℝ)
  have hea : (∑' k, a k) = ∑ k ∈ Finset.range (M+1), (V*z*D^3)^k/(k.factorial : ℝ) := by
    rw [tsum_eq_sum (s := Finset.range (M+1)) (by
      intro k hk
      have hh : ¬k ≤ M := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
      simp only [a, ite_eq_right hh])]
    apply Finset.sum_congr rfl
    intro k hk
    exact ite_eq_left (by have := Finset.mem_range.mp hk; omega)
  rw [show (∑ k ∈ Finset.range (packingNumber L+1), _) = ∑' k, a k by exact hea.symm,
    ← hb.tsum_eq]
  apply tsum_le_convolution (freeFamily_summable t d L) ha hb.summable
  intro n
  have hv := freeConfig_volume_le (ι := Fin n) ht L
  rw [Fintype.card_fin] at hv
  have hh := mul_le_mul_of_nonneg_right hv (pow_nonneg hz n)
  have hh' := div_le_div_of_nonneg_right hh (Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ n.factorial)
  rw [familyTerm, freeFamily_integral, Fintype.card_fin]
  apply hh'.trans
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  by_cases hc : k ≤ M ∧ n ≤ 4*k
  · simp only [show packingNumber L = M from rfl, ite_eq_left hc, a, ite_eq_left hc.1, b]
    rw [Nat.cast_choose ℝ hkn]
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have he : (((n.factorial : ℝ)/((k.factorial : ℝ)*((n-k).factorial : ℝ)))*V^k*
        ((k : ℝ)*w)^(n-k)*z^n)/(n.factorial : ℝ) =
        (V*z)^k/(k.factorial : ℝ)*((k : ℝ)^(n-k)*(w*z)^(n-k)/((n-k).factorial : ℝ)) := by
      have hzpow : z^n = z^k*z^(n-k) := by rw [← pow_add, Nat.add_sub_of_le hkn]
      rw [hzpow, mul_pow]
      field_simp
      ring
    change (((n.factorial : ℝ)/((k.factorial : ℝ)*((n-k).factorial : ℝ)))*V^k*
        ((k : ℝ)*w)^(n-k)*z^n)/(n.factorial : ℝ) ≤ _
    rw [he]
    have hkM : (k : ℝ) ≤ M := by exact_mod_cast hc.1
    have hp := power_trunc_bound (mul_nonneg hw hz) (show n-k ≤ 3*k by omega)
    have hpow : (k : ℝ)^(n-k)*(w*z)^(n-k) ≤ (M : ℝ)^(n-k)*D^(3*k) :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg k) hkM _) hp
        (pow_nonneg (mul_nonneg hw hz) _) (pow_nonneg (Nat.cast_nonneg M) _)
    have hm := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hpow (Nat.cast_nonneg (n-k).factorial))
      (div_nonneg (pow_nonneg (mul_nonneg hV hz) k) (Nat.cast_nonneg k.factorial))
    apply hm.trans_eq
    rw [mul_pow, pow_mul]
    ring
  · simp only [show packingNumber L = M from rfl, ite_eq_right hc, zero_mul, zero_div]
    apply mul_nonneg
    · dsimp only [a]
      split_ifs <;> positivity
    · dsimp only [b]
      positivity

end ContinuumTemperature
end

end OAI
