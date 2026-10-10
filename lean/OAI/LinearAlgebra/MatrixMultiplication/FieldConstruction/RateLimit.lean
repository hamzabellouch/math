import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.Witness
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.FiniteSchedule
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldRateLimit

open Filter
open scoped Topology

variable {F : Type*} [Field F]

structure HasRates (W : ℕ → AllFieldWitness F) (scale : ℕ → ℝ)
    (Y S R : ℝ) : Prop where
  scale_positive : ∀ᶠ n in atTop, 0 < scale n
  yield_limit : Tendsto (fun n => Real.log ((W n).multiplicity : ℝ) / scale n) atTop (𝓝 Y)
  volume_limit : Tendsto (fun n => Real.log ((W n).volume : ℝ) / scale n) atTop (𝓝 S)
  rank_limit : Tendsto (fun n => Real.log ((W n).rankBound : ℝ) / scale n) atTop (𝓝 R)

structure HasRateBounds (W : ℕ → AllFieldWitness F) (scale : ℕ → ℝ)
    (Y S R : ℝ) : Prop where
  scale_positive : ∀ᶠ n in atTop, 0 < scale n
  yield_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    Y - ε ≤ Real.log ((W n).multiplicity : ℝ) / scale n
  volume_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    S - ε ≤ Real.log ((W n).volume : ℝ) / scale n
  rank_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    Real.log ((W n).rankBound : ℝ) / scale n ≤ R + ε

theorem HasRates.toBounds {W : ℕ → AllFieldWitness F} {scale : ℕ → ℝ}
    {Y S R : ℝ} (h : HasRates W scale Y S R) : HasRateBounds W scale Y S R where
  scale_positive := h.scale_positive
  yield_lower ε hε := (h.yield_limit.eventually_const_lt (by linarith : Y - ε < Y)).mono
    (fun _ hn => hn.le)
  volume_lower ε hε := (h.volume_limit.eventually_const_lt (by linarith : S - ε < S)).mono
    (fun _ hn => hn.le)
  rank_upper ε hε := (h.rank_limit.eventually_lt_const (by linarith : R < R + ε)).mono
    (fun _ hn => hn.le)

theorem inequality_of_rates {W : ℕ → AllFieldWitness F} {scale : ℕ → ℝ}
    {Y S R : ℝ} (h : HasRates W scale Y S R) :
    Y + (Arithmetic.omega F / 3) * S ≤ R := by
  apply le_of_tendsto_of_tendsto
    (h.yield_limit.add (h.volume_limit.const_mul (Arithmetic.omega F / 3))) h.rank_limit
  filter_upwards [h.scale_positive] with n hn
  have hb := div_le_div_of_nonneg_right (W n).log_inequality hn.le
  simpa only [add_div, mul_div_assoc] using hb

theorem inequality_of_rateBounds {W : ℕ → AllFieldWitness F} {scale : ℕ → ℝ}
    {Y S R : ℝ} (h : HasRateBounds W scale Y S R) :
    Y + (Arithmetic.omega F / 3) * S ≤ R := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < ε / 3 := by positivity
  obtain ⟨n, hnscale, hnyield, hnvolume, hnrank⟩ :=
    (h.scale_positive.and ((h.yield_lower (ε / 3) hδ).and
      ((h.volume_lower (ε / 3) hδ).and (h.rank_upper (ε / 3) hδ)))).exists
  have hfinite := div_le_div_of_nonneg_right (W n).log_inequality hnscale.le
  simp only [add_div, mul_div_assoc] at hfinite
  have hω : 0 ≤ Arithmetic.omega F / 3 := div_nonneg Arithmetic.omega_nonneg (by norm_num)
  have hvolume := mul_le_mul_of_nonneg_left hnvolume hω
  have hωupper := mul_le_mul_of_nonneg_right
    (Arithmetic.omega_le_three (F := F)) hδ.le
  nlinarith

theorem omega_le_of_rates {W : ℕ → AllFieldWitness F} {scale : ℕ → ℝ}
    {Y S R : ℝ} (h : HasRates W scale Y S R) (positive : 0 < S) :
    Arithmetic.omega F ≤ 3 * (R - Y) / S := by
  apply (le_div_iff₀ positive).mpr
  have hb := inequality_of_rates h
  nlinarith

theorem omega_le_of_rateBounds {W : ℕ → AllFieldWitness F} {scale : ℕ → ℝ}
    {Y S R : ℝ} (h : HasRateBounds W scale Y S R) (positive : 0 < S) :
    Arithmetic.omega F ≤ 3 * (R - Y) / S := by
  apply (le_div_iff₀ positive).mpr
  have hb := inequality_of_rateBounds h
  nlinarith

structure FixedLotFamily (F : Type*) [Field F] where
  witness : ℕ → ℕ → AllFieldWitness F
  scale : ℕ → ℕ → ℝ
  yieldRate : ℕ → ℝ
  volumeRate : ℕ → ℝ
  rankRate : ℕ → ℝ
  bounds : ∀ j, HasRateBounds (witness j) (scale j)
    (yieldRate j) (volumeRate j) (rankRate j)

theorem inequality_of_fixedLotFamily (family : FixedLotFamily F) {Y S R : ℝ}
    (yield_limit : Tendsto family.yieldRate atTop (𝓝 Y))
    (volume_limit : Tendsto family.volumeRate atTop (𝓝 S))
    (rank_limit : Tendsto family.rankRate atTop (𝓝 R)) :
    Y + (Arithmetic.omega F / 3) * S ≤ R := by
  apply le_of_tendsto_of_tendsto'
    (yield_limit.add (volume_limit.const_mul (Arithmetic.omega F / 3))) rank_limit
  intro j
  exact inequality_of_rateBounds (family.bounds j)

theorem inequality_of_outer_families
    (family : ℕ → FixedLotFamily F) {Y S R : ℕ → ℝ} {Yfinal Sfinal Rfinal : ℝ}
    (yield_limit : ∀ K, Tendsto (family K).yieldRate atTop (𝓝 (Y K)))
    (volume_limit : ∀ K, Tendsto (family K).volumeRate atTop (𝓝 (S K)))
    (rank_limit : ∀ K, Tendsto (family K).rankRate atTop (𝓝 (R K)))
    (outer_yield : Tendsto Y atTop (𝓝 Yfinal))
    (outer_volume : Tendsto S atTop (𝓝 Sfinal))
    (outer_rank : Tendsto R atTop (𝓝 Rfinal)) :
    Yfinal + (Arithmetic.omega F / 3) * Sfinal ≤ Rfinal := by
  apply le_of_tendsto_of_tendsto'
    (outer_yield.add (outer_volume.const_mul (Arithmetic.omega F / 3))) outer_rank
  intro K
  exact inequality_of_fixedLotFamily (family K)
    (yield_limit K) (volume_limit K) (rank_limit K)

theorem omega_le_of_outer_families
    (family : ℕ → FixedLotFamily F) {Y S R : ℕ → ℝ} {Yfinal Sfinal Rfinal : ℝ}
    (yield_limit : ∀ K, Tendsto (family K).yieldRate atTop (𝓝 (Y K)))
    (volume_limit : ∀ K, Tendsto (family K).volumeRate atTop (𝓝 (S K)))
    (rank_limit : ∀ K, Tendsto (family K).rankRate atTop (𝓝 (R K)))
    (outer_yield : Tendsto Y atTop (𝓝 Yfinal))
    (outer_volume : Tendsto S atTop (𝓝 Sfinal))
    (outer_rank : Tendsto R atTop (𝓝 Rfinal)) (positive : 0 < Sfinal) :
    Arithmetic.omega F ≤ 3 * (Rfinal - Yfinal) / Sfinal := by
  apply (le_div_iff₀ positive).mpr
  have hb := inequality_of_outer_families family yield_limit volume_limit rank_limit
    outer_yield outer_volume outer_rank
  nlinarith

theorem staggered_rank_constraint
    (family : ∀ K : ℕ, 2 ≤ K → FixedLotFamily F) {H0 Cstar Sstar beta : ℝ}
    (yield_limit : ∀ K hK, Tendsto (family K hK).yieldRate atTop
      (𝓝 (H0 + Cstar - beta / (K : ℝ))))
    (volume_limit : ∀ K hK, Tendsto (family K hK).volumeRate atTop (𝓝 Sstar))
    (rank_limit : ∀ K hK, Tendsto (family K hK).rankRate atTop (𝓝 (8 * Real.log 7))) :
    H0 + Cstar + (Arithmetic.omega F / 3) * Sstar ≤ 8 * Real.log 7 := by
  have hfixed (K : ℕ) (hK : 2 ≤ K) :
      H0 + Cstar - beta / (K : ℝ) + Arithmetic.omega F * Sstar / 3 ≤
        8 * Real.log 7 := by
    have hb := inequality_of_fixedLotFamily (family K hK)
      (yield_limit K hK) (volume_limit K hK) (rank_limit K hK)
    convert hb using 1; ring
  have hb := FiniteSchedule.fixed_lot_boundary_limit hfixed
  convert hb using 1; ring

theorem omega_le_of_staggered_families
    (family : ∀ K : ℕ, 2 ≤ K → FixedLotFamily F) {H0 Cstar Sstar beta : ℝ}
    (yield_limit : ∀ K hK, Tendsto (family K hK).yieldRate atTop
      (𝓝 (H0 + Cstar - beta / (K : ℝ))))
    (volume_limit : ∀ K hK, Tendsto (family K hK).volumeRate atTop (𝓝 Sstar))
    (rank_limit : ∀ K hK, Tendsto (family K hK).rankRate atTop (𝓝 (8 * Real.log 7)))
    (positive : 0 < Sstar) :
    Arithmetic.omega F ≤ 3 * (8 * Real.log 7 - (H0 + Cstar)) / Sstar := by
  apply (le_div_iff₀ positive).mpr
  have hb := staggered_rank_constraint family yield_limit volume_limit rank_limit
  nlinarith

theorem omega_lt_of_staggered_families
    (family : ∀ K : ℕ, 2 ≤ K → FixedLotFamily F) {H0 Cstar Sstar beta target : ℝ}
    (yield_limit : ∀ K hK, Tendsto (family K hK).yieldRate atTop
      (𝓝 (H0 + Cstar - beta / (K : ℝ))))
    (volume_limit : ∀ K hK, Tendsto (family K hK).volumeRate atTop (𝓝 Sstar))
    (rank_limit : ∀ K hK, Tendsto (family K hK).rankRate atTop (𝓝 (8 * Real.log 7)))
    (positive : 0 < Sstar)
    (gap : 3 * (8 * Real.log 7 - (H0 + Cstar)) / Sstar < target) :
    Arithmetic.omega F < target :=
  lt_of_le_of_lt (omega_le_of_staggered_families family yield_limit volume_limit
    rank_limit positive) gap

end MatrixMultiplication.AllFieldRateLimit

end

end OAI
