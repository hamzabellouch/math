import OAI.NumberTheory.EgyptianFractions.FourierSecondMoment

namespace OAI
open scoped BigOperators
open ComplexConjugate

namespace Problem337

/-- Cauchy--Schwarz for the norm of a finite complex sum. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {α : Type*}
    (U : Finset α) (f : α → ℂ) :
    ‖∑ u ∈ U, f u‖ ^ 2 ≤ (U.card : ℝ) * ∑ u ∈ U, ‖f u‖ ^ 2 := by
  have hn := norm_sum_le U f
  have hs := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) (fun u => ‖f u‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

/-- Averaging equal column sums and bounding their pairwise correlations.
This is the finite algebraic core of van der Corput differencing. -/
theorem averaged_columns_correlation_bound {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ)
    (S : ℂ) (D E : ℝ)
    (hcol : ∀ t ∈ T, ∑ u ∈ U, z u t = S)
    (hdiag : ∀ t ∈ T, ∑ u ∈ U, ‖z u t‖ ^ 2 ≤ D)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * conj (z u s)‖ ≤ E) :
    (T.card : ℝ) ^ 2 * ‖S‖ ^ 2 ≤
      (U.card : ℝ) * ((T.card : ℝ) * D +
        (T.card : ℝ) * (T.card - 1 : ℝ) * E) := by
  classical
  have havg : (∑ u ∈ U, ∑ t ∈ T, z u t) = (T.card : ℂ) * S := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_congr rfl hcol]
    simp
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq U (fun u => ∑ t ∈ T, z u t)
  rw [havg, norm_mul, Complex.norm_natCast, mul_pow] at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [finite_complex_second_moment_identity]
  have hentry (t : β) (ht : t ∈ T) (s : β) (hs : s ∈ T) :
      (∑ u ∈ U, z u t * conj (z u s)).re ≤
        E + if t = s then D - E else 0 := by
    by_cases heq : t = s
    · subst s
      simp only [re_finset_sum, Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq, ite_true, add_sub_cancel]
      exact hdiag t ht
    · simpa [heq] using (Complex.re_le_norm _).trans (hcorr t ht s hs heq)
  calc
    (∑ t ∈ T, ∑ s ∈ T, (∑ u ∈ U, z u t * conj (z u s)).re) ≤
        ∑ t ∈ T, ∑ s ∈ T, (E + if t = s then D - E else 0) := by
      exact Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun s hs => hentry t ht s hs))
    _ = (T.card : ℝ) * D + (T.card : ℝ) * (T.card - 1 : ℝ) * E := by
      have hrow (t : β) (ht : t ∈ T) :
          (∑ s ∈ T, (E + if t = s then D - E else 0)) =
            (T.card : ℝ) * E + D - E := by
        simp [Finset.sum_add_distrib, ht]
        ring
      simp_rw [Finset.sum_congr rfl hrow]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Translation does not change a finite sum once the summation interval
    contains all translated points in its support. -/
theorem sum_shift_supported {M : Type*} [AddCommMonoid M]
    (a : ℤ → M) (N H : ℕ) (t : ℤ) (ht0 : 0 ≤ t) (htH : t ≤ H)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0) :
    (∑ n ∈ Finset.Icc (1 - (H : ℤ)) N, a (n + t)) =
      ∑ n ∈ Finset.Icc (1 : ℤ) N, a n := by
  classical
  apply Finset.sum_bij_ne_zero (fun n _ _ => n + t)
  · intro n hn hne
    by_contra hout
    exact hne (hsupport (n + t) hout)
  · intro n hn hn0 m hm hm0 heq
    omega
  · intro n hn hn0
    refine ⟨n - t, ?_, ?_, by omega⟩
    · simp only [Finset.mem_Icc] at hn ⊢
      omega
    · simpa using hn0
  · intros
    rfl

/-- A concrete finite-support shift bound, before using `H ≤ N` to simplify
    the two endpoint losses. Correlation assumptions are symmetric in the shift. -/
theorem van_der_corput_interval_exact
    (a : ℤ → ℂ) (N H : ℕ) (hH : 1 ≤ H) (E : ℝ) (hE : 0 ≤ E)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, -(H : ℤ) < h → h < H → h ≠ 0 →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ^ 2 ≤
      ((N : ℝ) + H) * ((N : ℝ) / H + E) := by
  classical
  let U := Finset.Icc (1 - (H : ℤ)) (N : ℤ)
  let T := Finset.range H
  let z : ℤ → ℕ → ℂ := fun n t => a (n + t)
  have hcardU : (U.card : ℝ) = (N : ℝ) + H := by
    dsimp [U]
    rw [Int.card_Icc]
    have heq : (N : ℤ) + 1 - (1 - (H : ℤ)) = ((N + H : ℕ) : ℤ) := by omega
    rw [heq]
    norm_cast
  have hcol (t : ℕ) (ht : t ∈ T) :
      (∑ n ∈ U, z n t) = ∑ n ∈ Finset.Icc (1 : ℤ) N, a n := by
    exact sum_shift_supported a N H t (by omega) (by have := Finset.mem_range.mp ht; omega) hsupport
  have hdiag (t : ℕ) (ht : t ∈ T) : (∑ n ∈ U, ‖z n t‖ ^ 2) ≤ (N : ℝ) := by
    have hs : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → ‖a n‖ ^ 2 = 0 := by
      intro n hn
      simp [hsupport n hn]
    have heq := sum_shift_supported (fun n => ‖a n‖ ^ 2) N H t
      (by omega) (by have := Finset.mem_range.mp ht; omega) hs
    change (∑ n ∈ U, ‖a (n + t)‖ ^ 2) ≤ (N : ℝ)
    rw [heq]
    calc
      (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖a n‖ ^ 2) ≤
          ∑ _n ∈ Finset.Icc (1 : ℤ) N, (1 : ℝ) := by
        exact Finset.sum_le_sum (fun n _ => by have := hnorm n; have := norm_nonneg (a n); nlinarith)
      _ = (N : ℝ) := by simp [Int.card_Icc]
  have hcorr' (t : ℕ) (ht : t ∈ T) (s : ℕ) (hs : s ∈ T) (hne : t ≠ s) :
      ‖∑ n ∈ U, z n t * conj (z n s)‖ ≤ E := by
    let b : ℤ → ℂ := fun n => a (n + ((t : ℤ) - s)) * conj (a n)
    have hb : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → b n = 0 := by
      intro n hn
      simp [b, hsupport n hn]
    have heq := sum_shift_supported b N H s (by omega)
      (by have := Finset.mem_range.mp hs; omega) hb
    have hz : (∑ n ∈ U, z n t * conj (z n s)) = ∑ n ∈ U, b (n + s) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [z, b]
    rw [hz, heq]
    apply hcorr
    · have := Finset.mem_range.mp ht
      have := Finset.mem_range.mp hs
      omega
    · have := Finset.mem_range.mp ht
      have := Finset.mem_range.mp hs
      omega
    · omega
  have hraw := averaged_columns_correlation_bound U T z
    (∑ n ∈ Finset.Icc (1 : ℤ) N, a n) N E hcol hdiag hcorr'
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  simp only [T, Finset.card_range, hcardU] at hraw
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hHR)).mp
  have hweak : (H : ℝ)^2 * ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖^2 ≤
      ((N : ℝ) + H) * ((H : ℝ) * N + (H : ℝ)^2 * E) := by
    apply hraw.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have heq : (((N : ℝ) + H) * ((N : ℝ) / H + E)) * (H : ℝ)^2 =
      ((N : ℝ) + H) * ((H : ℝ) * N + (H : ℝ)^2 * E) := by
    field_simp
  rw [heq]
  simpa [mul_comm] using hweak

/-- Opposite shifts give conjugate autocorrelations, with zero extension
    supplying the endpoint cancellation. -/
theorem interval_correlation_neg (a : ℤ → ℂ) (N : ℕ) (h : ℤ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + -h) * conj (a n)) =
      conj (∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)) := by
  classical
  rw [map_sum]
  apply Finset.sum_bij_ne_zero (fun n _ _ => n - h)
  · intro n hn hn0
    by_contra hout
    have hz := hsupport (n - h) hout
    simp [sub_eq_add_neg] at hz
    simp [hz] at hn0
  · intro n hn hn0 m hm hm0 heq
    omega
  · intro n hn hn0
    have hmem : n + h ∈ Finset.Icc (1 : ℤ) N := by
      by_contra hout
      have hz := hsupport (n + h) hout
      simp [hz] at hn0
    refine ⟨n + h, hmem, ?_, by omega⟩
    simpa [map_mul, mul_comm] using hn0
  · intro n hn hn0
    simp [map_mul, sub_eq_add_neg, mul_comm]

/-- The elementary van der Corput inequality for an interval-supported
    sequence, in the positive-shift form required for iterated differencing. -/
theorem van_der_corput_interval
    (a : ℤ → ℂ) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (E : ℝ) (hE : 0 ≤ E)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, 0 < h → h < H →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ^ 2 ≤
      2 * (N : ℝ)^2 / H + 2 * (N : ℝ) * E := by
  have hsym : ∀ h : ℤ, -(H : ℤ) < h → h < H → h ≠ 0 →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤ E := by
    intro h hl hu hn
    by_cases hp : 0 < h
    · exact hcorr h hp hu
    · have hneg : 0 < -h := by omega
      have hnegb : -h < (H : ℤ) := by omega
      have heq := interval_correlation_neg a N (-h) hsupport
      simp only [neg_neg] at heq
      rw [heq, Complex.norm_conj]
      exact hcorr (-h) hneg hnegb
  have hraw := van_der_corput_interval_exact a N H hH E hE hsupport hnorm hsym
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hHNR : (H : ℝ) ≤ N := by exact_mod_cast hHN
  calc
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ^ 2 ≤
        ((N : ℝ) + H) * ((N : ℝ) / H + E) := hraw
    _ ≤ (2 * (N : ℝ)) * ((N : ℝ) / H + E) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = 2 * (N : ℝ)^2 / H + 2 * (N : ℝ) * E := by ring

/-- Normalized van der Corput differencing, with an explicit absolute constant. -/
theorem van_der_corput_interval_normalized
    (a : ℤ → ℂ) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (E : ℝ) (hE : 0 ≤ E)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, 0 < h → h < H →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ^ 2 / (N : ℝ)^2 ≤
      2 / (H : ℝ) + 2 * E / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  apply (div_le_iff₀ (sq_pos_of_pos hNR)).mpr
  have hraw := van_der_corput_interval a N H hH hHN E hE hsupport hnorm hcorr
  have heq : (2 / (H : ℝ) + 2 * E / N) * (N : ℝ)^2 =
      2 * (N : ℝ)^2 / H + 2 * (N : ℝ) * E := by
    field_simp
  rw [heq]
  exact hraw

end Problem337

end OAI
