import OAI.NumberTheory.TwoPointCorrelations.HalaszGroupedEstimate
import OAI.NumberTheory.TwoPointCorrelations.HalaszBandSummation

namespace OAI

/-! Sum the actual geometric prime bands. The central terms retain the
Halász saving, and both kinds of error have summable band weights. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

theorem halasz_double_convolution_estimate : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b) → OneBounded f →
    ∀ (N m : ℕ) (L T V W M : ℝ), 2 ≤ N → 0 < m → m ≤ N →
      1 ≤ L → T ^ 2 ≤ L → B ≤ T → Real.log N ≤ V → 0 ≤ W → 0 ≤ M →
      (∀ t ∈ Set.Icc (-T) T,
        ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ V * Real.exp (-M)) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszDoubleConvolution f N L‖ ≤
        C * N * V * (M + 1) * Real.exp (-M) +
        C * N * W * Real.log N / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        C * m * Real.log (3 * N) ^ 2 := by
  obtain ⟨C₁, B, hC₁, hB, hanalytic⟩ := halasz_grouped_double_estimate
  obtain ⟨C₂, hC₂, htrivial⟩ := halasz_grouped_double_trivial
  obtain ⟨G, hG, hgeometric⟩ := halasz_band_saving_sum
  let D := C₁ + C₂
  let C := 1 + D * G + 2 * D + 2 / Real.log 2
  have hD : 0 < D := add_pos hC₁ hC₂
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hf1 hf hbound N m L T V W M hN hm hmN hL hTL hBT hNV hW hM hFA hFW
  let P := mrtPrimeBand L ((N : ℝ) / 2)
  let J := halaszBandIndex (Real.log (N : ℝ)) + 1
  let A := V * Real.exp (-M)
  let δ := (m : ℝ) / ((N : ℝ) + 1 / 2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNlog : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlog0 : 0 < Real.log (N : ℝ) := htwo.trans_le hNlog
  have hV : 0 ≤ V := hlog0.le.trans hNV
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < B) hBT
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hC₁D : C₁ ≤ D := by dsimp [D]; linarith
  have hC₂D : C₂ ≤ D := by dsimp [D]; linarith
  have hPl (p : ℕ) (hp : p ∈ P) : p.Prime := mrtPrimeBand_prime hp
  have hpbounds (p : ℕ) (hp : p ∈ P) : Real.log 2 ≤ Real.log ((N : ℝ) / p) ∧
      Real.log ((N : ℝ) / p) ≤ Real.log (N : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPl p hp).pos
    have hb := mrtPrimeBand_bounds (show 0 ≤ L by linarith) (by positivity) hp
    have hquot : (2 : ℝ) ≤ (N : ℝ) / p := (le_div_iff₀ hp0).mpr (by linarith)
    exact ⟨Real.log_le_log (by norm_num) hquot,
      Real.log_le_log (div_pos hN0 hp0) (div_le_self hN0.le (by exact_mod_cast (hPl p hp).one_le))⟩
  have hpart : halaszDoubleConvolution f N L =
      ∑ j ∈ range J, halaszGroupedDouble f N (halaszPrimeBandPart P N j) := by
    exact halasz_prime_band_partition P (fun p hp => (hpbounds p hp).2) _
  have hpiece (j : ℕ) : ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤
      D * N * min A (halaszBandScale j) +
      D * N * halaszBandScale j * W / (δ * T) +
      (m : ℝ) / halaszBandScale j * Real.log (3 * N) ^ 2 := by
    let v := halaszBandScale j
    have hv : Real.log 2 ≤ v := halasz_band_scale_ge_log_two j
    have hv0 : 0 < v := htwo.trans_le hv
    have hPb : ∀ p ∈ halaszPrimeBandPart P N j, p.Prime ∧
        v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v := by
      intro p hp
      exact ⟨hPl p (mem_filter.mp hp).1,
        halasz_prime_band_part_bounds P (fun p hp => (hpbounds p hp).1) hp⟩
    have hPbig : ∀ p ∈ halaszPrimeBandPart P N j, p.Prime ∧ T ^ 2 ≤ (p : ℝ) ∧
        v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v := by
      intro p hp
      have hpp := (mem_filter.mp hp).1
      have hb := mrtPrimeBand_bounds (show 0 ≤ L by linarith) (by positivity) hpp
      exact ⟨(hPb p hp).1, hTL.trans hb.1.le, (hPb p hp).2⟩
    have ht := htrivial f hbound N v (by omega) hv _ hPb
    have ha := hanalytic f hf1 hf hbound N m v T A W hN hm hmN hv hBT hA hW _ hPbig hFA hFW
    have htD : ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤ D * N * v :=
      ht.trans (by gcongr)
    have haD : ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤
        D * N * A + D * N * v * W / (δ * T) + (m : ℝ) / v * Real.log (3 * N) ^ 2 :=
      ha.trans (by gcongr)
    change ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤
      D * N * min A v + D * N * v * W / (δ * T) + (m : ℝ) / v * Real.log (3 * N) ^ 2
    by_cases hvA : v ≤ A
    · rw [min_eq_right hvA]
      have herr : 0 ≤ D * N * v * W / (δ * T) + (m : ℝ) / v * Real.log (3 * N) ^ 2 := by positivity
      linarith
    · rw [min_eq_left (le_of_not_ge hvA)]
      exact haD
  have htop : halaszBandScale J ≤ 2 * Real.log (N : ℝ) := by
    have hb := (halasz_band_scale_bounds hNlog).1
    have he : halaszBandScale J = 2 * halaszBandScale (halaszBandIndex (Real.log (N : ℝ))) := by
      dsimp [J, halaszBandScale]
      rw [pow_succ]
      ring
    rw [he]
    linarith
  have hmin := hgeometric J V M hV hM (htop.trans (by linarith))
  have hscales := (halasz_band_scale_sum_le J).trans htop
  have hinverses := halasz_band_inverse_sum_le J
  have hsum : ‖halaszDoubleConvolution f N L‖ ≤
      (D * N) * (∑ j ∈ range J, min A (halaszBandScale j)) +
      (D * N * W / (δ * T)) * (∑ j ∈ range J, halaszBandScale j) +
      ((m : ℝ) * Real.log (3 * N) ^ 2) * (∑ j ∈ range J, (halaszBandScale j)⁻¹) := by
    rw [hpart]
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum (fun j _ => hpiece j)).trans_eq
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have hc1 : D * G ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ 2 / Real.log 2 by positivity]
  have hc2 : 2 * D ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ D * G by positivity, show 0 ≤ 2 / Real.log 2 by positivity]
  have hc3 : 2 / Real.log 2 ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ D * G by positivity]
  calc
    _ ≤ _ := hsum
    _ ≤ (D * N) * (G * V * (M + 1) * Real.exp (-M)) +
        (D * N * W / (δ * T)) * (2 * Real.log (N : ℝ)) +
        ((m : ℝ) * Real.log (3 * N) ^ 2) * (2 / Real.log 2) := by
      gcongr
    _ = (D * G) * N * V * (M + 1) * Real.exp (-M) +
        (2 * D) * N * W * Real.log N / (δ * T) +
        (2 / Real.log 2) * m * Real.log (3 * N) ^ 2 := by ring
    _ ≤ _ := by gcongr

end TwoPointCorrelations

end OAI
