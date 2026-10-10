import OAI.NumberTheory.EgyptianFractions.FourierSecondMoment
import OAI.NumberTheory.EgyptianFractions.FejerBounds

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.FejerSampleMean

/-- Translating the samples rotates every Fourier coefficient without changing
its norm. -/
theorem norm_sum_character_translate {q : ℕ} [NeZero q] {I : Type*}
    [Fintype I] (x : I → ZMod q) (a y : ZMod q) :
    ‖∑ t : I, ZMod.stdAddChar (a * (x t - y))‖ =
      ‖∑ t : I, ZMod.stdAddChar (a * x t)‖ := by
  simp_rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul, norm_mul]
  simp

/-- Negating a frequency conjugates its coefficient. -/
theorem norm_sum_character_neg {q : ℕ} [NeZero q] {I : Type*}
    [Fintype I] (x : I → ZMod q) (a : ZMod q) :
    ‖∑ t : I, ZMod.stdAddChar ((-a) * x t)‖ =
      ‖∑ t : I, ZMod.stdAddChar (a * x t)‖ := by
  simp_rw [neg_mul, AddChar.map_neg_eq_conj]
  rw [← map_sum (starRingEnd ℂ) (fun t : I => ZMod.stdAddChar (a * x t)) Finset.univ]
  exact Complex.norm_conj _

/-- Off-diagonal correlations of the geometric packet are controlled by the
positive low frequencies, with no unmentioned negative-frequency assumption. -/
theorem packet_correlation_bound {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] (x : I → ZMod q) (y : ZMod q) (E : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤ E)
    (j k : Fin h) (hjk : j ≠ k) :
    ‖∑ t : I, ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)) *
      (starRingEnd ℂ) (ZMod.stdAddChar ((k.val : ZMod q) * (x t - y)))‖ ≤ E := by
  have heq (t : I) :
      ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)) *
          (starRingEnd ℂ) (ZMod.stdAddChar ((k.val : ZMod q) * (x t - y))) =
        ZMod.stdAddChar (((j.val : ZMod q) - (k.val : ZMod q)) * (x t - y)) := by
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [heq]
  rw [norm_sum_character_translate]
  have hne : j.val ≠ k.val := by intro he; exact hjk (Fin.ext he)
  by_cases hkj : k.val ≤ j.val
  · have hc : ((j.val : ZMod q) - (k.val : ZMod q)) = ((j.val - k.val : ℕ) : ZMod q) :=
      (Nat.cast_sub hkj).symm
    rw [hc]
    exact hfourier (j.val - k.val) (by omega) (by omega)
  · have hc : ((j.val : ZMod q) - (k.val : ZMod q)) = -((k.val - j.val : ℕ) : ZMod q) := by
      rw [Nat.cast_sub (by omega : j.val ≤ k.val)]
      ring
    rw [hc, norm_sum_character_neg]
    exact hfourier (k.val - j.val) (by omega) (by omega)

/-- Lower counterpart of the finite second-moment bound, using the same
honest off-diagonal correlation hypotheses. -/
theorem second_moment_lower {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) (E : ℝ)
    (hunit : ∀ u ∈ U, ∀ t ∈ T, ‖z u t‖ = 1)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * (starRingEnd ℂ) (z u s)‖ ≤ E) :
    (U.card : ℝ) * T.card - (T.card : ℝ) * (T.card - 1 : ℝ) * E ≤
      ∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2 := by
  classical
  rw [finite_complex_second_moment_identity]
  have hentry (t : β) (ht : t ∈ T) (s : β) (hs : s ∈ T) :
      -E + (if t = s then (U.card : ℝ) + E else 0) ≤
        (∑ u ∈ U, z u t * (starRingEnd ℂ) (z u s)).re := by
    by_cases hts : t = s
    · subst s
      have hd : (∑ u ∈ U, z u t * (starRingEnd ℂ) (z u t)).re = U.card := by
        simp only [re_finset_sum, Complex.mul_conj, Complex.ofReal_re]
        calc
          (∑ u ∈ U, Complex.normSq (z u t)) = ∑ _u ∈ U, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Complex.normSq_eq_norm_sq, hunit u hu t ht]
            norm_num
          _ = _ := by simp
      simp [hd]
    · have hc := hcorr t ht s hs hts
      have hn := Complex.re_le_norm (-(∑ u ∈ U, z u t * (starRingEnd ℂ) (z u s)))
      simp only [Complex.neg_re, norm_neg] at hn
      simp only [ite_eq_right hts, add_zero]
      linarith
  calc
    _ = ∑ t ∈ T, ∑ s ∈ T, (-E + if t = s then (U.card : ℝ) + E else 0) := by
      have hrow (t : β) (ht : t ∈ T) :
          (∑ s ∈ T, (-E + if t = s then (U.card : ℝ) + E else 0)) =
            -(T.card : ℝ) * E + (U.card : ℝ) + E := by
        simp [Finset.sum_add_distrib, ht]
        ring
      simp_rw [Finset.sum_congr rfl hrow]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun s hs => hentry t ht s hs))

/-- The lower sampled mean of the geometric packet, before identifying the
packet with the named kernel. -/
theorem raw_packet_mean_lower {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] [Nonempty I] (hh : 0 < h)
    (x : I → ZMod q) (y : ZMod q) (ε : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤
        (Fintype.card I : ℝ) * ε) :
    1 - ((h : ℝ) - 1) * ε ≤
      (∑ t : I, ‖∑ j : Fin h,
        ZMod.stdAddChar ((j.val : ZMod q) * (x t - y))‖ ^ 2 / (h : ℝ)) /
        (Fintype.card I : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hraw := second_moment_lower Finset.univ Finset.univ
    (fun t : I => fun j : Fin h => ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)))
    ((Fintype.card I : ℝ) * ε)
    (fun _ _ _ _ => by simp)
    (fun j _ k _ hjk => packet_correlation_bound x y _ hfourier j k hjk)
  simp only [Finset.card_univ, Fintype.card_fin] at hraw
  rw [← Finset.sum_div]
  apply (le_div_iff₀ hI).2
  apply (le_div_iff₀ hhR).2
  calc
    _ = (Fintype.card I : ℝ) * h -
        (h : ℝ) * ((h : ℝ) - 1) * ((Fintype.card I : ℝ) * ε) := by ring
    _ ≤ _ := hraw

/-- The upper sampled mean, paired with the preceding lower estimate. -/
theorem raw_packet_mean_upper {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] [Nonempty I] (hh : 0 < h)
    (x : I → ZMod q) (y : ZMod q) (ε : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤
        (Fintype.card I : ℝ) * ε) :
    (∑ t : I, ‖∑ j : Fin h,
      ZMod.stdAddChar ((j.val : ZMod q) * (x t - y))‖ ^ 2 / (h : ℝ)) /
      (Fintype.card I : ℝ) ≤ 1 + ((h : ℝ) - 1) * ε := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hraw := finite_complex_second_moment_bound Finset.univ Finset.univ
    (fun t : I => fun j : Fin h => ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)))
    ((Fintype.card I : ℝ) * ε)
    (fun _ _ _ _ => by simp)
    (fun j _ k _ hjk => packet_correlation_bound x y _ hfourier j k hjk)
  simp only [Finset.card_univ, Fintype.card_fin] at hraw
  rw [← Finset.sum_div]
  apply (div_le_iff₀ hI).2
  apply (div_le_iff₀ hhR).2
  calc
    _ ≤ (Fintype.card I : ℝ) * h +
        (h : ℝ) * ((h : ℝ) - 1) * ((Fintype.card I : ℝ) * ε) := hraw
    _ = _ := by ring

theorem packet_eq_kernel {q h : ℕ} [NeZero q] (x : ZMod q) :
    ‖∑ j : Fin h, ZMod.stdAddChar ((j.val : ZMod q) * x)‖ ^ 2 / (h : ℝ) =
      GeometricKernel.kernel h (ZMod.stdAddChar x) := by
  unfold GeometricKernel.kernel
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ZMod.stdAddChar ((j : ZMod q) * x)) h,
    GeometricKernel.cyclic_geometric_sum_eq]

/-- Low-frequency cancellation implies the expected lower mass at every
center of the named Fejér kernel. -/
theorem fejer_sample_mean_lower {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] [Nonempty I] (hh : 0 < h)
    (x : I → ZMod q) (y : ZMod q) (ε : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤
        (Fintype.card I : ℝ) * ε) :
    1 - ((h : ℝ) - 1) * ε ≤
      (∑ t : I, GeometricKernel.kernel h (ZMod.stdAddChar (x t - y))) /
        (Fintype.card I : ℝ) := by
  simpa only [packet_eq_kernel] using raw_packet_mean_lower hh x y ε hfourier

/-- Two-sided sampled mean estimate for the named kernel. -/
theorem fejer_sample_mean_error {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] [Nonempty I] (hh : 0 < h)
    (x : I → ZMod q) (y : ZMod q) (ε : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤
        (Fintype.card I : ℝ) * ε) :
    |(∑ t : I, GeometricKernel.kernel h (ZMod.stdAddChar (x t - y))) /
        (Fintype.card I : ℝ) - 1| ≤ ((h : ℝ) - 1) * ε := by
  have hlo := fejer_sample_mean_lower hh x y ε hfourier
  have hhi := raw_packet_mean_upper hh x y ε hfourier
  simp only [packet_eq_kernel] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Equivalent input convention phrased as normalized Fourier averages. -/
theorem fejer_sample_mean_error_of_normalized {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] [Nonempty I] (hh : 0 < h)
    (x : I → ZMod q) (y : ZMod q) (ε : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖(∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)) /
        (Fintype.card I : ℂ)‖ ≤ ε) :
    |(∑ t : I, GeometricKernel.kernel h (ZMod.stdAddChar (x t - y))) /
        (Fintype.card I : ℝ) - 1| ≤ ((h : ℝ) - 1) * ε := by
  apply fejer_sample_mean_error hh x y ε
  intro l hl hlh
  have h := hfourier l hl hlh
  rw [norm_div, Complex.norm_natCast] at h
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  simpa only [mul_comm] using (div_le_iff₀ hI).mp h

end Problem337.FejerSampleMean

end

end OAI
