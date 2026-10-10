import OAI.NumberTheory.TwoPoint.Halasz.HalaszNearScales
import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalNearEnergy

namespace OAI

/-! The near-frequency energy estimate, with the distance
hypotheses at the original cutoff and the actual typical-set error. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

lemma halasz_log_error_square (L : ℝ) (hL : 1 ≤ L) :
    (Real.log L / L) ^ 2 ≤ 2 * L ^ (-1 / (16 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hh := log_sq_le_two_mul L hL
  have hr : 1 / L ≤ L ^ (-1 / (16 : ℝ)) := by
    simpa only [Real.rpow_neg_one, one_div] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (-1 : ℝ) ≤ -1 / 16)
  calc
    _ = Real.log L ^ 2 / L ^ 2 := div_pow _ _ _
    _ ≤ (2 * L) / L ^ 2 := div_le_div_of_nonneg_right hh (sq_nonneg L)
    _ = 2 * (1 / L) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by norm_num)

theorem halasz_centered_typical_energy : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ X : ℕ, N ≤ 2 * X → X ≤ N ^ 3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (t T M : ℝ), 0 ≤ M → |t| + Real.log (2 * N : ℕ) ^ 8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      squaredDistance F (mrtArchimedeanTwist t) X ≤ Real.log (Real.log X) / 10 →
      ∀ {ι : Type} (J : Finset ι) (P : ι → Finset ℕ),
      (∫ u in -((Real.log N) ^ (1 / (16 : ℝ)))..((Real.log N) ^ (1 / (16 : ℝ))),
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N (t + u)‖ ^ 2) ≤
        48 * Real.exp 1 *
          (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N +
        C * (Real.exp (-M) + (Real.log N) ^ (-1 / (16 : ℝ))) := by
  obtain ⟨C₀, hC₀, hcenter⟩ := halasz_centered_prefix
  let D : ℝ := 36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8
  let C : ℝ := 400 * Real.pi * C₀ ^ 2 + 200 * D ^ 2
  have hD : 0 < D := by dsimp [D, halaszPrimePowerLogConstant]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hL : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hcenter, halasz_near_prefix_uniform, hL, eventually_ge_atTop 2]
    with N hcenter hnear hLN hN2
  intro X hNX hXN F hF1 hFm hFb t T M hM hT hd hsmall ι J P
  let G := halaszTwistedFunction F t
  let L := Real.log (N : ℝ)
  let R := Real.log L / L
  let U := L ^ (1 / (16 : ℝ))
  let A := C₀ * (Real.exp (-M / 2) + R)
  let E := D * L ^ (-1 / (16 : ℝ))
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hR : 0 ≤ R := div_nonneg (Real.log_nonneg hLN) hL0.le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hU : 0 < U := Real.rpow_pos_of_pos hL0 _
  have hUN : U ≤ (N : ℝ) := by
    calc
      U ≤ L := Real.rpow_le_self_of_one_le hLN (by norm_num)
      _ ≤ (N : ℝ) := by
        have hh := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) by exact_mod_cast (show 0 < N by omega))
        dsimp [L]
        linarith
  have hc : ∀ k ∈ Icc N (2 * N), ‖halaszPhaseMean G 0 k‖ ≤ A * k :=
    hcenter X hNX hXN F hF1 hFm hFb t T M hM hT hd
  have hn : ∀ u ∈ Set.Icc (-U) U, ∀ k ∈ Icc N (2 * N),
      ‖halaszPhaseMean G u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean G 0 k‖ ≤ E * k := by
    intro u hu k hk
    exact hnear X hNX hXN F hF1 hFm hFb t hsmall u (abs_le.mpr hu) k hk
  have hh := halasz_typical_near_energy J P G (halasz_twisted_oneBounded F hFb t)
    (by omega : 0 < N) A E U hA hE hU hc hn
  have hpoly (u : ℝ) : mrtDyadicPolynomial (mrtTypicalCoefficient J P G) N u =
      mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N (t + u) := by
    dsimp [G]
    rw [halasz_typical_twist, halasz_twisted_dyadic]
  simp_rw [hpoly] at hh
  have hmain : 100 * Real.pi * A ^ 2 + 200 * U * E ^ 2 ≤
      C * (Real.exp (-M) + L ^ (-1 / (16 : ℝ))) := by
    have hexp : Real.exp (-M / 2) ^ 2 = Real.exp (-M) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hs := halasz_log_error_square L hLN
    have hsum : (Real.exp (-M / 2) + R) ^ 2 ≤
        2 * (Real.exp (-M) + 2 * L ^ (-1 / (16 : ℝ))) := by
      change (Real.exp (-M / 2) + Real.log L / L) ^ 2 ≤ _
      nlinarith [sq_nonneg (Real.exp (-M / 2) - Real.log L / L)]
    have he : U * E ^ 2 = D ^ 2 * L ^ (-1 / (16 : ℝ)) := by
      have hp : L ^ (1 / (16 : ℝ)) * L ^ (-1 / (16 : ℝ)) = 1 := by
        rw [← Real.rpow_add hL0]
        norm_num
      dsimp [U, E]
      calc
        _ = D ^ 2 * (L ^ (1 / (16 : ℝ)) * L ^ (-1 / (16 : ℝ))) * L ^ (-1 / (16 : ℝ)) := by ring
        _ = _ := by rw [hp]; ring
    rw [mul_assoc (200 : ℝ) U (E ^ 2), he]
    have hm := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ 100 * Real.pi * C₀ ^ 2 by positivity)
    dsimp [A, C]
    nlinarith [mul_nonneg (sq_nonneg D) (Real.exp_pos (-M)).le,
      mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg C₀)) (Real.exp_pos (-M)).le]
  apply hh.trans
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hratio : U / (N : ℝ) ≤ 1 := (div_le_one hNr).mpr hUN
  have hbad : 0 ≤ (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) := by positivity
  have hexc : 16 * Real.exp 1 * (U / N + 2) *
      (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N ≤
      48 * Real.exp 1 * (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N := by
    calc
      _ ≤ 16 * Real.exp 1 * 3 *
          (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N := by
        gcongr
        linarith
      _ = _ := by ring
  calc
    _ = 16 * Real.exp 1 * (U / N + 2) *
        (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N +
        (100 * Real.pi * A ^ 2 + 200 * U * E ^ 2) := by ring
    _ ≤ _ := add_le_add hexc hmain

end TwoPointCorrelations

end OAI
