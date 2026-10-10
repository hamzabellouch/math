import OAI.NumberTheory.TwoPointCorrelations.HalaszMeanValue
import OAI.NumberTheory.TwoPointCorrelations.HalaszCorrectionTransfer
import OAI.NumberTheory.TwoPointCorrelations.HalaszCorrectionScale
import OAI.NumberTheory.TwoPointCorrelations.HalaszDistanceDecay

namespace OAI

/-! The ordinary Halász estimate for general normalized multiplicative
functions. Only the values at primes enter the pretentious hypothesis. -/

namespace TwoPointCorrelations

open Finset Filter

lemma halasz_complete_distance (f : ℕ → ℂ) (g : ℕ → ℂ) (N : ℕ) :
    squaredDistance (mrtCompletePart f) g N = squaredDistance f g N := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p hp
  have hprime : p.Prime := (mem_filter.mp hp).2
  have he : mrtCompletePart f p = f p := by
    simpa using mrtCompletePart_prime_pow f hprime 1
  rw [he]

theorem halasz_general_mean_value : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (f : ℕ → ℂ), f 1 = 1 → Multiplicative f → OneBounded f →
    ∀ (M : ℝ), 0 ≤ M →
      (∀ t ∈ Set.Icc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8),
        M ≤ squaredDistance f (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, f n‖ ≤ C * N *
        ((M + 1) * Real.exp (-M) + Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C₀, Y₀, hC₀, hmean⟩ := halasz_mean_value
  obtain ⟨K, hK, hcut⟩ := halasz_distance_cutoff_loss
  let D := C₀ * Real.exp K + 3 * C₀ + 1
  let C := mrtCorrectionBound * D
  have hCorr : 0 < mrtCorrectionBound := Real.exp_pos _
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := mul_pos hCorr hD
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (halasz_eventually_correction_scale Y₀)
  refine ⟨C, X₀, hC, ?_⟩
  intro N hXN f hf1 hf hb M hM hd
  obtain ⟨hW, hWY, hWN, htail, hlog, hll⟩ := hX₀ N hXN
  let W := ⌈Real.log (N : ℝ) ^ 4⌉₊
  let M' := max 0 (M - K)
  let E := (M + 1) * Real.exp (-M)
  let R := Real.log (Real.log (N : ℝ)) / Real.log N
  let A := C₀ * (Real.exp K * E + 3 * R)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hNlog : 0 < Real.log (N : ℝ) := by linarith
  have hprefix (d : ℕ) (hdN : d ∈ Icc 1 N) (hdW : d ≤ W) :
      ‖∑ n ∈ Icc 1 (N / d), mrtCompletePart f n‖ ≤ A * ((N / d : ℕ) : ℝ) := by
    have hd0 : 0 < d := (mem_Icc.mp hdN).1
    have hWNnat : W ^ 2 ≤ N := by exact_mod_cast hWN
    obtain ⟨hWq, hqN, hNq⟩ := halasz_correction_quotient hW hd0 hdW hWNnat
    have hq2 : 2 ≤ N / d := hW.trans hWq
    have hqY : Y₀ ≤ ((N / d : ℕ) : ℝ) :=
      hWY.trans (by exact_mod_cast hWq)
    have hlnq : 0 < Real.log ((N / d : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N / d by omega))
    have hlogqN : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < N / d by omega)) (by exact_mod_cast hqN)
    have hheight : Real.log ((N / d : ℕ) : ℝ) ^ 8 ≤ Real.log (N : ℝ) ^ 8 :=
      pow_le_pow_left₀ hlnq.le hlogqN 8
    have hdist (t : ℝ) (ht : t ∈ Set.Icc
        (-(Real.log ((N / d : ℕ) : ℝ) ^ 8)) (Real.log ((N / d : ℕ) : ℝ) ^ 8)) :
        M' ≤ squaredDistance (mrtCompletePart f) (mrtArchimedeanTwist t) (N / d) := by
      rw [halasz_complete_distance]
      apply max_le
      · exact halasz_distance_nonneg f hb _ t
      · have hl := hcut f hb (N / d) N hq2 hqN hNq t
        have hu := hd t ⟨by linarith [ht.1], ht.2.trans hheight⟩
        linarith
    have hm := hmean (N / d) hqY (mrtCompletePart f) (fromPrimePowers_one _)
      (fun a b ha hb => mrtCompletePart_mul f ha hb) (mrtCompletePart_oneBounded f hb)
      M' (le_max_left _ _) hdist
    have hdec := halasz_decay_shift hM hK
    have herr := halasz_log_error_cutoff hq2 hqN hNq (by linarith)
    calc
      _ ≤ C₀ * ((N / d : ℕ) : ℝ) *
          ((M' + 1) * Real.exp (-M') +
            Real.log (Real.log ((N / d : ℕ) : ℝ)) / Real.log ((N / d : ℕ) : ℝ)) := hm
      _ ≤ C₀ * ((N / d : ℕ) : ℝ) * (Real.exp K * E + 3 * R) := by gcongr
      _ = _ := by ring
  have hc := halasz_correction_mean_bound f hf hb hf1 N W (by omega) A hA hprefix
  have hRtail : (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ R := by
    apply htail.trans
    exact div_le_div_of_nonneg_right hll hNlog.le
  have hsmall : A + (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ D * (E + R) := by
    dsimp [A, D]
    have hCE : 0 ≤ C₀ * Real.exp K * R := by positivity
    have h3E : 0 ≤ 3 * C₀ * E := by positivity
    nlinarith
  calc
    _ ≤ mrtCorrectionBound * N * (A + (W : ℝ) ^ (-(1 / 4 : ℝ))) := hc
    _ ≤ mrtCorrectionBound * N * (D * (E + R)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by dsimp [C, E, R]; ring

end TwoPointCorrelations

end OAI
