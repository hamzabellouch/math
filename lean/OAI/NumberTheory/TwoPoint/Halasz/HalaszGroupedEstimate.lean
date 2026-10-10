import OAI.NumberTheory.TwoPoint.Halasz.HalaszGroupedBounds
import OAI.NumberTheory.TwoPoint.Fourier.ModFivePsiDecay

namespace OAI

/-! Apply the full triple-convolution estimate to one actual logarithmic
band, with its adaptive denominator and finite cofactor prime cutoff. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical LSeries.notation

theorem halasz_grouped_double_estimate : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) → OneBounded f →
    ∀ (N m : ℕ) (v T A W : ℝ), 2 ≤ N → 0 < m → m ≤ N → Real.log 2 ≤ v →
      B ≤ T → 0 ≤ A → 0 ≤ W →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ) ∧
      v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v) →
      (∀ t ∈ Set.Icc (-T) T, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszGroupedDouble f N P‖ ≤ C * N * A +
        C * N * v * W / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        (m : ℝ) / v * Real.log (3 * N) ^ 2 := by
  obtain ⟨C₀, B, hC₀, hB, htriple⟩ := halasz_prime_triple_estimate
  obtain ⟨K, hK, hweights⟩ := halasz_band_mean_square_weights
  let U := 1 + 2 * halaszMertensConstant / Real.log 2
  let V := 2 + halaszMertensConstant / Real.log 2
  let C := 2 * C₀ * K + 80 * U * V
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := halaszMertensConstant_nonneg
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hf1 hf hbound N m v T A W hN hm hmN hv hBT hA hW P hP hFA hFW
  let x : ℝ := (N : ℝ) + 1 / 2
  let Q := sievePrimesUpTo (Real.exp (2 * v))
  let a := fun p : ℕ => f p / (Real.log ((N : ℝ) / p) : ℂ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxle : x ≤ 2 * N := by
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [x]
    linarith
  have hv0 : 0 < v := htwo.trans_le hv
  have hT : 0 < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < B) hBT
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmle : (m : ℝ) ≤ x := by
    have hmr : (m : ℝ) ≤ N := by exact_mod_cast hmN
    dsimp [x]
    linarith
  have hPl : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hPb : ∀ p ∈ P, p.Prime ∧ v ≤ Real.log ((N : ℝ) / p) ∧
      Real.log ((N : ℝ) / p) < 2 * v := fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩
  have hQl : ∀ q ∈ Q, q.Prime := fun q hq => sievePrimesUpTo_prime _ q hq
  have hQb : ∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ Real.exp (2 * v) := fun q hq =>
    ⟨hQl q hq, sievePrimesUpTo_le _ (Real.exp_pos _).le q hq⟩
  have hPsub : P ⊆ Icc 1 N := by
    intro p hp
    have he := (halasz_log_band_endpoints hN0 (hPl p hp) (hP p hp).2.2.1 (hP p hp).2.2.2).2
    have hdiv : (N : ℝ) / Real.exp v ≤ N :=
      div_le_self hN0.le (Real.one_le_exp_iff.mpr hv0.le)
    exact mem_Icc.mpr ⟨(hPl p hp).pos, by exact_mod_cast he.trans hdiv⟩
  have hcover : ∀ p ∈ P, ∀ q, q.Prime → q ≤ N / p → q ∈ Q := by
    intro p hp q hq hqN
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPl p hp).pos
    have hcut : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self N p
    have hy0 : 0 < (N : ℝ) / p := div_pos hN0 hp0
    have hupper := (Real.log_lt_iff_lt_exp hy0).mp (hP p hp).2.2.2
    have hqr : (q : ℝ) ≤ Real.exp (2 * v) := (by exact_mod_cast hqN : (q : ℝ) ≤ ((N / p : ℕ) : ℝ)).trans
      (hcut.trans hupper.le)
    exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (Real.exp_pos _).le).mpr hqr), hq⟩
  have ha : ∀ p ∈ P, ‖a p‖ ≤ v⁻¹ := fun p hp =>
    halasz_adaptive_coefficient_bound f hbound hv0 (hPl p hp).pos (hP p hp).2.2.1
  have hb : ∀ q ∈ Q, ‖f q‖ ≤ 1 := fun q hq => hbound q (hQl q hq).pos
  have hestimate := htriple f hf1 hf hbound N x T A W (v⁻¹) m hx hm hmle
    (modFive_half_cutoff_nonnat N) hBT hA hW (inv_nonneg.mpr hv0.le) P Q
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩) hQl a f ha hb hFA hFW
  have heqa : (fun p : ℕ => (Real.log (p : ℝ) : ℂ) * a p) =
      fun p : ℕ => (Real.log (p : ℝ) : ℂ) * f p / (Real.log ((N : ℝ) / p) : ℂ) := by
    funext p
    dsimp [a]
    ring
  rw [show ⌊x⌋₊ = N from modFive_half_cutoff_floor N, heqa,
    halasz_grouped_triple_prefix f N P Q hPsub hQl hcover] at hestimate
  have hweight := hweights f hbound N v hN0 hv P Q hPb hQb
  have hpMass : (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ U * v :=
    halasz_log_band_mass_linear hN0 hv P hPb
  have hqMass : (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ V * v := by
    have hq := halasz_prime_set_mass_le (Y := Real.exp (2 * v))
      (Real.one_le_exp_iff.mpr (by linarith)) Q hQb
    rw [Real.log_exp] at hq
    have hscale := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ halaszMertensConstant / Real.log 2 from div_nonneg hM htwo.le)
    rw [div_mul_cancel₀ _ htwo.ne'] at hscale
    dsimp [V]
    linarith
  have hp0 : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) / p := sum_nonneg (fun p hp =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hPl p hp).one_le)) (Nat.cast_nonneg _))
  have hq0 : 0 ≤ ∑ q ∈ Q, Real.log (q : ℝ) / q := sum_nonneg (fun q hq =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hQl q hq).one_le)) (Nat.cast_nonneg _))
  have hsmall : v⁻¹ * (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ U := by
    apply (mul_le_mul_of_nonneg_left hpMass (inv_nonneg.mpr hv0.le)).trans_eq
    field_simp
  have hprod : (v⁻¹ * ∑ p ∈ P, Real.log (p : ℝ) / p) *
      (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ U * (V * v) :=
    mul_le_mul hsmall hqMass hq0 hU.le
  have hlog : Real.log (x + m) ^ 2 ≤ Real.log (3 * N) ^ 2 := by
    have hmr : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    apply pow_le_pow_left₀ (Real.log_nonneg (by dsimp [x]; linarith))
    exact Real.log_le_log (by positivity) (by dsimp [x]; linarith)
  have hcmain : 2 * C₀ * K ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ 80 * U * V by positivity]
  have hctail : 80 * U * V ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ 2 * C₀ * K by positivity]
  change ‖halaszGroupedDouble f N P‖ ≤ _ at hestimate ⊢
  calc
    _ ≤ _ := hestimate
    _ ≤ (C₀ * (2 * N) * A) * K +
        40 * (2 * N) * (U * (V * v)) * W / ((m / x) * T) +
        v⁻¹ * Real.log (3 * N) ^ 2 * m := by
      apply add_le_add
      · apply add_le_add
        · calc
            _ ≤ (C₀ * x * A) * K := mul_le_mul_of_nonneg_left hweight (by positivity)
            _ ≤ _ := by gcongr
        · calc
            _ = (40 * x * W / ((m / x) * T)) *
                ((v⁻¹ * ∑ p ∈ P, Real.log (p : ℝ) / p) *
                  (∑ q ∈ Q, Real.log (q : ℝ) / q)) := by ring
            _ ≤ (40 * x * W / ((m / x) * T)) * (U * (V * v)) :=
              mul_le_mul_of_nonneg_left hprod (by positivity)
            _ ≤ (40 * (2 * N) * W / ((m / x) * T)) * (U * (V * v)) := by
              gcongr
            _ = _ := by ring
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hv0.le)) (Nat.cast_nonneg m)
    _ ≤ C * N * A + C * N * v * W / ((m / x) * T) +
        (m : ℝ) / v * Real.log (3 * N) ^ 2 := by
      have hfirst := mul_le_mul_of_nonneg_right hcmain (show 0 ≤ (N : ℝ) * A by positivity)
      have hlast := mul_le_mul_of_nonneg_right hctail
        (show 0 ≤ (N : ℝ) * v * W / ((m / x) * T) by positivity)
      ring_nf at hfirst hlast ⊢
      linarith

end TwoPointCorrelations

end OAI
