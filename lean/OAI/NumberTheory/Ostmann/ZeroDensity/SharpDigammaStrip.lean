import OAI.NumberTheory.Ostmann.ZeroDensity.DigammaTailEstimate

namespace OAI

/-! # The leading logarithm of digamma on the required positive strip

The bounded remainder, rather than a multiple of the logarithm, preserves the
correct length in the approximate functional equation for the fourth moment.
-/

namespace Ostmann

open Complex
open scoped BigOperators

 theorem sharp_digamma_strip (z : ℂ) (hz : 1 / 8 ≤ z.re) (hz3 : z.re ≤ 3) :
    ‖Complex.digamma z - (Real.log (|z.im| + 2) : ℂ)‖ ≤
      59 + |Real.eulerMascheroniConstant| := by
  let Y := |z.im|
  let N : ℕ := ⌈Y⌉₊ + 1
  let H : ℝ := harmonic N
  have hY : 0 ≤ Y := abs_nonneg _
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNlo : Y + 1 ≤ (N : ℝ) := by
    have h := Nat.le_ceil Y
    dsimp [N]
    push_cast
    linarith
  have hNhi : (N : ℝ) ≤ Y + 2 := by
    have h := Nat.ceil_lt_add_one hY
    dsimp [N]
    push_cast
    linarith
  have hpos : 0 < z.re := by linarith
  have hnorm (m : ℕ) : (Y + 1) / 9 ≤ ‖z + m‖ := by
    have hr := Complex.re_le_norm (z + m)
    have hi := Complex.abs_im_le_norm (z + m)
    simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im, add_zero] at hr hi
    dsimp [Y]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hhead : ‖∑ m ∈ Finset.range N, (z + m)⁻¹‖ ≤ 18 := by
    have hp (m : ℕ) : ‖(z + m)⁻¹‖ ≤ 9 / (Y + 1) := by
      rw [norm_inv]
      have hh := one_div_le_one_div_of_le (by positivity : 0 < (Y + 1) / 9) (hnorm m)
      rw [← one_div (‖z + m‖)]
      simpa only [one_div_div] using hh
    apply (norm_sum_le _ _).trans
    have hs := Finset.sum_le_sum (s := Finset.range N) (fun m _ => hp m)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    apply hs.trans
    have hn : (N : ℝ) * 9 ≤ 18 * (Y + 1) := by nlinarith
    have hdiv := (div_le_iff₀ (by positivity : 0 < Y + 1)).mpr hn
    convert hdiv using 1
    ring
  have htail : ‖∑' i : ℕ, densityDigammaTerm z (i + N)‖ ≤ 40 := by
    apply (density_digamma_tail_bound z hz N hN).trans
    apply (div_le_iff₀ hNpos).mpr
    have hzn := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hpos] at hzn
    dsimp [Y] at hNlo hY ⊢
    nlinarith
  have hHlo : Real.log (Y + 2) ≤ H := by
    have h := log_add_one_le_harmonic N
    have hle : Real.log (Y + 2) ≤ Real.log (N + 1 : ℕ) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    exact hle.trans h
  have hHhi : H ≤ 1 + Real.log (Y + 2) := by
    exact (harmonic_le_one_add_log N).trans
      (add_le_add_right (Real.log_le_log hNpos hNhi) 1)
  have hHnorm : ‖((H : ℂ) - (Real.log (Y + 2) : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  have hsum := density_digamma_hasSum z hpos
  have hsplit := hsum.summable.sum_add_tsum_nat_add N
  have hfirst : (∑ m ∈ Finset.range N, densityDigammaTerm z m) =
      (H : ℂ) - ∑ m ∈ Finset.range N, (z + m)⁻¹ := by
    simp only [densityDigammaTerm, Finset.sum_sub_distrib]
    rw [Complex.sum_inv_natCast_add_one]
    norm_cast
  rw [hfirst, hsum.tsum_eq] at hsplit
  have hid : Complex.digamma z - (Real.log (Y + 2) : ℂ) =
      (((H : ℂ) - (Real.log (Y + 2) : ℂ)) -
        ∑ m ∈ Finset.range N, (z + m)⁻¹) +
          (∑' i : ℕ, densityDigammaTerm z (i + N)) - (Real.eulerMascheroniConstant : ℂ) := by
    linear_combination -hsplit
  change ‖Complex.digamma z - (Real.log (Y + 2) : ℂ)‖ ≤ _
  rw [hid]
  calc
    _ ≤ (‖(H : ℂ) - (Real.log (Y + 2) : ℂ)‖ +
      ‖∑ m ∈ Finset.range N, (z + m)⁻¹‖) +
      ‖∑' i : ℕ, densityDigammaTerm z (i + N)‖ + ‖(Real.eulerMascheroniConstant : ℂ)‖ := by
      calc
        _ ≤ (‖((H : ℂ) - (Real.log (Y + 2) : ℂ)) -
            ∑ m ∈ Finset.range N, (z + m)⁻¹‖ +
            ‖∑' i : ℕ, densityDigammaTerm z (i + N)‖) +
            ‖(Real.eulerMascheroniConstant : ℂ)‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
        _ ≤ _ := add_le_add_left (add_le_add_left (norm_sub_le _ _) _) _
    _ ≤ _ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith

end Ostmann

end OAI
