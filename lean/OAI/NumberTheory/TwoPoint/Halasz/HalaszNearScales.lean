import OAI.NumberTheory.TwoPoint.Halasz.HalaszCenteredPrefix

namespace OAI

/-! The near-center comparison is uniform on every prefix of the actual
dyadic interval, with the pretentious condition at the original cutoff. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical ComplexConjugate

lemma halasz_loglog_power_cutoff (N X : ℕ) (hN : 2 ≤ N) (hX2 : 2 ≤ X) (hX : X ≤ N ^ 3) :
    Real.log (Real.log X) ≤ Real.log (Real.log N) + Real.log 3 := by
  have hX1 : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh := Real.log_le_log (zero_lt_one.trans hX1)
    (show (X : ℝ) ≤ (N : ℝ) ^ 3 by exact_mod_cast hX)
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hh' := Real.log_le_log (Real.log_pos hX1) hh
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hLN.ne'] at hh'
  linarith

/-- Small distance at X suffices for every prefix in `[N,2N]`, without
redefining the minimizing twist at each prefix. -/
theorem halasz_near_prefix_uniform :
    ∀ᶠ N : ℕ in atTop, ∀ X : ℕ, N ≤ 2 * X → X ≤ N ^ 3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) X ≤
        Real.log (Real.log X) / 10 →
      ∀ u : ℝ, |u| ≤ (Real.log N) ^ (1 / (16 : ℝ)) →
      ∀ k ∈ Icc N (2 * N),
      ‖halaszPhaseMean (halaszTwistedFunction F t) u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)) *
          halaszPhaseMean (halaszTwistedFunction F t) 0 k‖ ≤
        (36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8) *
          (Real.log N) ^ (-1 / (16 : ℝ)) * k := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp halasz_near_renormalization
  obtain ⟨B, hB, hcut⟩ := halasz_distance_cutoff_loss
  have hLL : ∀ᶠ N : ℕ in atTop, 4 * Real.log 3 + 40 * B ≤ Real.log (Real.log (N : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (4 * Real.log 3 + 40 * B))
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop 4, hLL] with N hNK hN2 hLLN
  intro X hNX hXN F hF1 hFm hFb t hD u hu k hk
  have hNk := (mem_Icc.mp hk).1
  have hX2 : 2 ≤ X := by omega
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hLNk : Real.log (N : ℝ) ≤ Real.log k := Real.log_le_log hN0 (by exact_mod_cast hNk)
  have hLLNk : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log k) :=
    Real.log_le_log hLN hLNk
  have hLLX := halasz_loglog_power_cutoff N X (by omega) hX2 hXN
  have hDk : squaredDistance F (mrtArchimedeanTwist t) k ≤ Real.log (Real.log k) / 8 := by
    have hupp : squaredDistance F (mrtArchimedeanTwist t) k ≤
        squaredDistance F (mrtArchimedeanTwist t) X + B := by
      by_cases hkX : k ≤ X
      · have hm := halasz_distance_monotone F hFb t hkX
        linarith
      · have hXk : X ≤ k := by omega
        have hkc : k ≤ X ^ 3 := by
          have hsq : 4 ≤ X ^ 2 := by nlinarith
          calc
            k ≤ 2 * N := (mem_Icc.mp hk).2
            _ ≤ 4 * X := by omega
            _ ≤ X * X ^ 2 := by nlinarith
            _ = X ^ 3 := by ring
        exact hcut F hFb X k hX2 hXk hkc t
    linarith
  have huk : |u| ≤ (Real.log k) ^ (1 / (16 : ℝ)) := hu.trans
    (Real.rpow_le_rpow hLN.le hLNk (by norm_num))
  have hh := hK k (hNK.trans hNk) F hF1 hFm hFb ∅ (by simp) (by simp) t hDk u huk
  have he : mrtMissingCoefficient F ∅ = F := by
    funext n
    simp [mrtMissingCoefficient, mrtPrimeMask, mrtPrimeAvoids]
  rw [he] at hh
  apply hh.trans
  have hr := Real.rpow_le_rpow_of_nonpos hLN hLNk (by norm_num : (-1 / (16 : ℝ)) ≤ 0)
  have hc : 0 ≤ 36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8 := by
    unfold halaszPrimePowerLogConstant
    positivity
  calc
    _ ≤ (36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8) * k *
        (Real.log N) ^ (-1 / (16 : ℝ)) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
