import OAI.NumberTheory.DirichletL.IdealMangoldt

namespace OAI

namespace SevenEighths.IdealLogDerivative

open ActualEisensteinCubic UniqueFactorizationMonoid IdealEuler
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical Topology

noncomputable section

def coeff (a : Ideal O →*₀ ℂ) (n : ℕ) : ℂ :=
  ShortDraftHeckeBridge.normFiberCoeff (fun I => (IdealMangoldt.value I : ℂ) * a I) n

theorem norm_coeff_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) (n : ℕ) :
    ‖coeff a n‖ ≤ IdealMangoldt.coeff (fun _ => 1) n := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg I), one_mul]
  exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg I) (ha I)

theorem norm_coeff_le_two_vonMangoldt (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (n : ℕ) :
    ‖coeff a n‖ ≤ 2 * ArithmeticFunction.vonMangoldt n :=
  (norm_coeff_le a ha n).trans
    (IdealMangoldt.coeff_le_two_vonMangoldt (fun _ => 1) (fun _ => le_refl _) n)

theorem coeff_summable (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (coeff a) s := by
  apply Summable.of_norm
  have h := (IdealMangoldt.coeff_LSeriesSummable (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_refl _) hs).norm
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.coeff_nonneg (fun _ => 1) (fun _ => zero_le_one) n)]
    using norm_coeff_le a ha n

theorem primePow_coprime_factor {B C : Ideal O} (h : IsPrimePow (B * C))
    (hBC : IsRelPrime B C) : B = 1 ∨ C = 1 := by
  obtain ⟨P, k, hP, hk, heq⟩ := h
  obtain ⟨i, hi, hBi⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_right B C)
  obtain ⟨j, hj, hCj⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_left C B)
  have hB := associated_iff_eq.mp hBi
  have hC := associated_iff_eq.mp hCj
  by_cases hi0 : i = 0
  · left; simpa only [hi0, pow_zero] using hB
  by_cases hj0 : j = 0
  · right; simpa only [hj0, pow_zero] using hC
  exact (hP.not_isUnit (hBC (hB ▸ dvd_pow_self P hi0) (hC ▸ dvd_pow_self P hj0))).elim

theorem value_mul_coprime {B C : Ideal O} (hBC : IsRelPrime B C) :
    IdealMangoldt.value (B * C) =
      (if C = 1 then IdealMangoldt.value B else 0) +
      (if B = 1 then IdealMangoldt.value C else 0) := by
  by_cases hB : B = 1
  · subst B
    simp only [one_mul, IdealMangoldt.value_one, ite_self, ite_true, zero_add]
  by_cases hC : C = 1
  · subst C
    simp only [mul_one, IdealMangoldt.value_one, ite_self, ite_true, add_zero]
  have hnot : ¬IsPrimePow (B * C) := by
    intro h
    exact (primePow_coprime_factor h hBC).elim hB hC
  simp only [IdealMangoldt.value, hnot, hB, hC, ite_false, zero_add]

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem sum_value_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (∑ D ∈ idealDivisors (P ^ k), (IdealMangoldt.value D : ℂ)) =
      k * (Real.log (Ideal.absNorm P) : ℂ) := by
  rw [idealDivisors_prime_pow P hP k, Finset.sum_image]
  · induction k with
    | zero => simp only [Nat.zero_add, Finset.sum_range_one, pow_zero,
        IdealMangoldt.value_one, Complex.ofReal_zero, Nat.cast_zero, zero_mul]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, IdealMangoldt.value_pow hP (Nat.succ_pos k)]
      push_cast
      ring
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_isUnit hP.ne_zero hij

theorem sum_value_mul (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsRelPrime B C) :
    (∑ D ∈ idealDivisors (B * C), (IdealMangoldt.value D : ℂ)) =
      (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) +
      ∑ D ∈ idealDivisors C, (IdealMangoldt.value D : ℂ) := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  have h1B : (1 : Ideal O) ∈ idealDivisors B := (mem_idealDivisors hB).mpr (one_dvd _)
  have h1C : (1 : Ideal O) ∈ idealDivisors C := (mem_idealDivisors hC).mpr (one_dvd _)
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  calc
    _ = ∑ D ∈ idealDivisors B, ∑ E ∈ idealDivisors C,
        ((if E = 1 then (IdealMangoldt.value D : ℂ) else 0) +
        (if D = 1 then (IdealMangoldt.value E : ℂ) else 0)) := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      rw [value_mul_coprime ((hBC.of_dvd_left ((mem_idealDivisors hB).mp hD)).of_dvd_right
        ((mem_idealDivisors hC).mp hE)), Complex.ofReal_add]
      split_ifs <;> rfl
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel,
        Finset.sum_ite_eq', ite_eq_left h1C, ite_eq_left h1B, Finset.sum_const_zero]

theorem sum_value_divisors (B : Ideal O) (hB : B ≠ 0) :
    (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact (hB rfl).elim
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, idealDivisors_one, Finset.sum_singleton]
    simp only [IdealMangoldt.value_one, map_one, Nat.cast_one, Real.log_one]
  | hpr k hP =>
    rw [sum_value_prime_pow _ hP k, map_pow, Nat.cast_pow, Real.log_pow]
    push_cast
    rfl
  | @hcp B C hBC ihB ihC =>
    have hB0 : B ≠ 0 := left_ne_zero_of_mul hB
    have hC0 : C ≠ 0 := right_ne_zero_of_mul hB
    rw [sum_value_mul B C hB0 hC0 hBC, ihB hB0, ihC hC0, map_mul, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hB0))
        (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hC0)), Complex.ofReal_add]

theorem value_le_log_norm (B : Ideal O) :
    IdealMangoldt.value B ≤ Real.log (Ideal.absNorm B) := by
  by_cases h : IsPrimePow B
  · obtain ⟨P, k, hP, hk, rfl⟩ := h
    rw [IdealMangoldt.value_pow hP hk, map_pow, Nat.cast_pow, Real.log_pow]
    apply le_mul_of_one_le_left
    · exact Real.log_natCast_nonneg _
    · exact_mod_cast hk
  · rw [IdealMangoldt.value, ite_eq_right h]
    exact Real.log_natCast_nonneg _

theorem weighted_eq_term (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    weighted a s B = LSeries.term (fun _ => a B) s (Ideal.absNorm B) := by
  by_cases hB : B = 0
  · subst B
    simp only [map_zero, LSeries.term_zero]
  · have hn : Ideal.absNorm B ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB
    change a B * CubicEisenstein.fullIdealWeight s B = _
    simp only [CubicEisenstein.fullIdealWeight, hB, ite_false,
      LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

theorem weighted_hasDerivAt (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    HasDerivAt (fun z => weighted a z B)
      (-((Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)) s := by
  simp_rw [weighted_eq_term]
  convert LSeries.hasDerivAt_term (fun _ => a B) (Ideal.absNorm B) s using 1
  by_cases hn : Ideal.absNorm B = 0
  · simp only [hn, LSeries.term_zero, mul_zero]
  · simp only [LSeries.term_of_ne_zero hn, LSeries.logMul, Complex.natCast_log,
      mul_div_assoc]

theorem log_weighted_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => (Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)
      (-deriv (series a) s) := by
  obtain ⟨x, hx, hxs⟩ := exists_between hs
  have hu := weighted_summable_norm a ha (x : ℂ) (by simpa using hx)
  have hd (B : Ideal O) : DifferentiableOn ℂ (fun z => weighted a z B) {z : ℂ | x < z.re} :=
    fun z _ => (weighted_hasDerivAt a z B).differentiableAt.differentiableWithinAt
  have hU : IsOpen {z : ℂ | x < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hbound (B : Ideal O) (z : ℂ) (hz : z ∈ {z : ℂ | x < z.re}) :
      ‖weighted a z B‖ ≤ ‖weighted a (x : ℂ) B‖ := by
    simp only [weighted_eq_term]
    exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hz.le) _
  have H := Complex.hasSum_deriv_of_summable_norm hu hd hU hbound hxs
  simp_rw [(weighted_hasDerivAt a s _).deriv] at H
  unfold IdealEuler.series
  simpa only [neg_neg] using H.neg

theorem mangoldt_weighted_summable_norm (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun B : Ideal O => ‖(IdealMangoldt.value B : ℂ) * weighted a s B‖) := by
  apply (log_weighted_hasSum a ha s hs).summable.norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro B
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg B), abs_of_nonneg (Real.log_natCast_nonneg _)]
  exact mul_le_mul_of_nonneg_right (value_le_log_norm B) (norm_nonneg _)

theorem mangoldt_series_eq_LSeries (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * weighted a s B) = LSeries (coeff a) s := by
  have H := (mangoldt_weighted_summable_norm a ha s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' B : {B : Ideal O // Ideal.absNorm B = n},
    (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) _ at H
  have hf (n : ℕ) : (∑' B : {B : Ideal O // Ideal.absNorm B = n},
      (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) = LSeries.term (coeff a) s n := by
    unfold coeff
    simpa only [weighted, normWeight,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mul_assoc]
      using SmoothMobiusCorrection.idealDirichlet_fiber
        (fun B => (IdealMangoldt.value B : ℂ) * a B) s n
  simp_rw [hf] at H
  exact H.tsum_eq.symm

theorem mulFiber_value_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : CompletedGauss.MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  let e := CompletedGauss.mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, (IdealMangoldt.value D.val : ℂ) :=
      e.tsum_eq (fun D => (IdealMangoldt.value D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (IdealMangoldt.value D : ℂ))).symm
    _ = _ := sum_value_divisors B hB

theorem coeff_LSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s * series a s = -deriv (series a) s := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (IdealMangoldt.value p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (mangoldt_weighted_summable_norm a ha s hs).mul_norm
    (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : CompletedGauss.MulFiber B, F p.val) =
      (Real.log (Ideal.absNorm B) : ℂ) * f B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : CompletedGauss.MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : CompletedGauss.MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_value_sum B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : CompletedGauss.MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  calc
    _ = (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * f B) * ∑' B : Ideal O, f B := by
      rw [mangoldt_series_eq_LSeries a ha s hs]
      rfl
    _ = ∑' p : Ideal O × Ideal O, ((IdealMangoldt.value p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (mangoldt_weighted_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = -deriv (series a) s := hsum.unique (log_weighted_hasSum a ha s hs)

theorem coeff_LSeries_eq_neg_logDeriv (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv (series a) s / series a s := by
  apply (eq_div_iff (series_ne_zero a ha s hs)).mpr
  exact coeff_LSeries_mul_series a ha s hs

theorem coeff_LSeries_eq_neg_logDeriv_of_eq (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 1 < z.re → F z = series a z)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv F s / F s := by
  have hd : deriv F s = deriv (series a) s := by
    apply Filter.EventuallyEq.deriv_eq
    have hU : {z : ℂ | 1 < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hU] with z hz
    exact hF z hz
  rw [hd, hF s hs]
  exact coeff_LSeries_eq_neg_logDeriv a ha s hs

end
end SevenEighths.IdealLogDerivative

end OAI
