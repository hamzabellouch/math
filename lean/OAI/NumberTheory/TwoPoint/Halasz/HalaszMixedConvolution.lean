import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeTruncation

namespace OAI

/-! Logarithmic convolution for a typical coefficient. Only multiplication
by primes above the deleted bands is used. The prime coefficient and the
remaining typical coefficient are kept distinct. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszRawPrimeTerm (B : ℕ → ℂ) (N p : ℕ) : ℂ :=
  (Real.log (p:ℝ):ℂ) * ∑ m ∈ Icc 1 (N/p), B (p*m)

noncomputable def halaszMixedPrimeConvolution (G B : ℕ → ℂ) (N : ℕ) (L U : ℝ) : ℂ :=
  ∑ p ∈ mrtPrimeBand L U,
    (Real.log (p:ℝ):ℂ)*G p*(∑ m ∈ Icc 1 (N/p), B m)

lemma halasz_raw_logarithmic_sum (B : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) =
      ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d:ℂ)*
        ∑ m ∈ Icc 1 (N/d), B (d*m) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.vonMangoldt p.1:ℂ)*B (p.1*p.2) := by
      apply sum_congr rfl
      intro n _
      rw [Nat.sum_divisorsAntidiagonal (fun a b =>
        (ArithmeticFunction.vonMangoldt a:ℂ)*B (a*b))]
      have he : (∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d:ℂ)*B n) =
          B n*(Real.log (n:ℝ):ℂ) := by
        rw [← sum_mul, ← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]
        ring
      rw [← he]
      apply sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    _ = ∑ p ∈ halaszHyperbola N,
        (ArithmeticFunction.vonMangoldt p.1:ℂ)*B (p.1*p.2) :=
      halasz_sum_divisorsAntidiagonal
        (fun a b => (ArithmeticFunction.vonMangoldt a:ℂ)*B (a*b)) N
    _ = _ := by
      rw [halasz_hyperbola_rows
        (fun a b => (ArithmeticFunction.vonMangoldt a:ℂ)*B (a*b)) N]
      apply sum_congr rfl
      intro d _
      rw [mul_sum]

lemma halasz_raw_row_bound (B : ℕ → ℂ) (hB : OneBounded B)
    (N d : ℕ) (hd : 0 < d) :
    ‖∑ m ∈ Icc 1 (N/d), B (d*m)‖ ≤ (N:ℝ)/d := by
  have hdiv : ((N/d:ℕ):ℝ) ≤ (N:ℝ)/d := by
    apply (le_div_iff₀ (show (0:ℝ)<d by exact_mod_cast hd)).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  calc
    _ ≤ ∑ _m ∈ Icc 1 (N/d), (1:ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum (fun m hm =>
        hB (d*m) (Nat.mul_pos hd (mem_Icc.mp hm).1)))
    _ = ((N/d:ℕ):ℝ) := by simp
    _ ≤ _ := hdiv

lemma halasz_raw_prime_term_bound (B : ℕ → ℂ) (hB : OneBounded B)
    (N p : ℕ) (hp : p.Prime) :
    ‖halaszRawPrimeTerm B N p‖ ≤ (N:ℝ)*(Real.log (p:ℝ)/p) := by
  have hl : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  rw [halaszRawPrimeTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hl]
  calc
    _ ≤ Real.log (p:ℝ)*((N:ℝ)/p) :=
      mul_le_mul_of_nonneg_left (halasz_raw_row_bound B hB N p hp.pos) hl
    _ = _ := by ring

lemma halasz_raw_prime_power_error (B : ℕ → ℂ) (hB : OneBounded B) (N : ℕ) :
    ‖(∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, halaszRawPrimeTerm B N p‖ ≤
        (N:ℝ)*halaszPrimePowerConstant := by
  rw [halasz_raw_logarithmic_sum, sum_filter, ← sum_sub_distrib]
  have he (d:ℕ) : (ArithmeticFunction.vonMangoldt d:ℂ)*
      (∑ m ∈ Icc 1 (N/d), B (d*m)) -
      (if d.Prime then halaszRawPrimeTerm B N d else 0) =
      (halaszPrimePowerWeight d:ℂ)*(∑ m ∈ Icc 1 (N/d), B (d*m)) := by
    by_cases hd : d.Prime
    · simp [hd,halaszRawPrimeTerm,halaszPrimePowerWeight,
        ArithmeticFunction.vonMangoldt_apply_prime hd]
    · simp [hd,halaszPrimePowerWeight]
  simp_rw [he]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (N:ℝ)*(halaszPrimePowerWeight d/d) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro d hd
      have hw := halaszPrimePowerWeight_nonneg d
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      calc
        _ ≤ halaszPrimePowerWeight d*((N:ℝ)/d) :=
          mul_le_mul_of_nonneg_left
            (halasz_raw_row_bound B hB N d (mem_Icc.mp hd).1) hw
        _ = _ := by ring
    _ = (N:ℝ)*∑ d ∈ Icc 1 N, halaszPrimePowerWeight d/d := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (halaszPrimePowerWeight_summable.sum_le_tsum _
        (fun d _ => div_nonneg (halaszPrimePowerWeight_nonneg d) (Nat.cast_nonneg d)))
      (Nat.cast_nonneg N)

lemma halasz_raw_prime_band_error (B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ N) :
    ‖(∑ p ∈ (Icc 1 N).filter Nat.Prime, halaszRawPrimeTerm B N p) -
      ∑ p ∈ mrtPrimeBand L N, halaszRawPrimeTerm B N p‖ ≤
        (N:ℝ)*(Real.log L+halaszMertensConstant) := by
  have hnat : (Icc 1 N).filter Nat.Prime = sievePrimesUpTo (N:ℝ) := by
    ext p
    simp only [mem_filter,mem_Icc,sievePrimesUpTo,Nat.floor_natCast,mem_Iic]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.pos,h.1⟩,h.2⟩⟩
  rw [hnat, mrtPrimeBand, sum_sdiff_eq_sub (mrt_sievePrimesUpTo_mono hLN),
    sub_sub_cancel]
  calc
    _ ≤ (N:ℝ)*∑ p ∈ sievePrimesUpTo L, Real.log (p:ℝ)/p := by
      rw [mul_sum]
      exact (norm_sum_le _ _).trans (sum_le_sum (fun p hp =>
        halasz_raw_prime_term_bound B hB N p (sievePrimesUpTo_prime L p hp)))
    _ ≤ _ := mul_le_mul_of_nonneg_left (halasz_prime_prefix_mass_le hL) (Nat.cast_nonneg N)

theorem halasz_mixed_logarithmic_approximation (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ N)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    ‖(∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      halaszMixedPrimeConvolution G B N L N‖ ≤
        (N:ℝ)*(halaszPrimePowerConstant+Real.log L+halaszMertensConstant) := by
  have hmixed : (∑ p ∈ mrtPrimeBand L N, halaszRawPrimeTerm B N p) =
      halaszMixedPrimeConvolution G B N L N := by
    unfold halaszMixedPrimeConvolution halaszRawPrimeTerm
    apply sum_congr rfl
    intro p hp
    have hpl := (mrtPrimeBand_bounds (by linarith) (Nat.cast_nonneg N) hp).1
    rw [mul_assoc]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    exact hmul p (mrtPrimeBand_prime hp) hpl m (mem_Icc.mp hm).1
  have hp := halasz_raw_prime_power_error B hB N
  have hl := halasz_raw_prime_band_error B hB N hL hLN
  rw [hmixed] at hl
  have hh := norm_add_le
    ((∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, halaszRawPrimeTerm B N p)
    ((∑ p ∈ (Icc 1 N).filter Nat.Prime, halaszRawPrimeTerm B N p) -
      halaszMixedPrimeConvolution G B N L N)
  rw [sub_add_sub_cancel] at hh
  nlinarith

end TwoPointCorrelations

end OAI
