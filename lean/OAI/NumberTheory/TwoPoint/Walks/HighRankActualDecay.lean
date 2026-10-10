import OAI.NumberTheory.TwoPoint.Walks.HighRankCatalogCost
import OAI.NumberTheory.TwoPoint.Walks.RankDecay

namespace OAI

/-! The actual column/padding catalog is exponentially negligible at the manuscript scales. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_actual_high_rank_decay (h : ℕ) (Cj Cm Cw : ℝ)
    (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (J R M Q D B H : ℕ) (P : Fin J → Finset ℕ) (Qp : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
      (forward : Fin R → Bool) (j : Fin J) (perfect : Finset (Fin R)) (cut : Fin R)
      (base : ColumnPrimeAssignment J R P → (Fin R → ℕ) → ℤ)
      (weight : ColumnPrimeAssignment J R P × (Fin R → ℕ) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass Qp ≤ L ^ (2 : ℕ) → 1 ≤ primeHarmonicMass (P j) →
      (∀ p ∈ P j, p.Prime) → (∀ p ∈ P j, H ≤ p) → (∀ p ∈ P j, p ≤ B) →
      (Q : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (B : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, a.2 i ≤ Q) →
      (∀ a ∈ F, ∀ i, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ∀ i, Squarefree (a.2 i)) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors ⊆ Qp) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors.card ≤ M) →
      (∀ a ∈ F, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward a.2 j)
        (by change 0 < R; omega) h perfect cut ⌊L ^ (1 / 50 : ℝ)⌋₊) →
      (∀ a ∈ F, ∀ i ∈ perfect, ((a.1 j i).val : ℤ) ∣ base a.1 a.2 +
        wordDisplacement h ((columnTupleWord a.1 forward a.2).take i.val)) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∀ a ∈ F, weight a ≤ W) →
      (∑ a ∈ F, weight a * columnReciprocalWeight a.1 *
        ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹) ≤
          Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  let K := Cw + 2 * (3 + 7 * Cm + 4 * Cj) + 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hK2 : 2 ≤ K := by dsimp [K]; linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_rank_floor_bounds, eventually_column_minor_size_exp h,
    eventually_rank_log_budget 105 (by norm_num),
    eventually_high_rank_total K hK] with L hL hlog hr hminor hlogminor hdecay
  intro J R M Q D B H P Qp F forward j perfect cut base weight W
    hR hRL hJ hM hT hRp hmass hQmass hV hprime hlo hB hQ hD hBexp hH
    hq hd hsq hpool hcount hrank hlit hW hWexp hweight
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hU : 1 ≤ L ^ (2 : ℕ) := one_le_pow₀ hL
  have hHp : (0 : ℝ) < H := (Real.exp_pos _).trans_le hH
  have hHN : 0 < H := by exact_mod_cast hHp
  let r := ⌊L ^ (1 / 50 : ℝ)⌋₊
  let saving := Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
    (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)
  let cost := W * (((Fintype.card (CrudeColumnPatternCode J R) : ℝ) * (L ^ (2 : ℕ)) ^ (R * J)) *
    ((∑ n : Fin (R * M + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) *
      (L ^ (2 : ℕ)) ^ (R * M)))
  have hc : cost ≤ Real.exp (K * L * (Real.log L) ^ 2) := by
    have hb := column_padding_catalog_cost_exp_bound J R M L Cj Cm (L ^ (2 : ℕ))
      hR hLp hlog hJ hM hT hRp hU le_rfl
    have hb' : (3 + 7 * Cm + 4 * Cj) * R * (Real.log L) ^ 2 ≤
        2 * (3 + 7 * Cm + 4 * Cj) * L * (Real.log L) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hRL
        (show 0 ≤ (3 + 7 * Cm + 4 * Cj) * (Real.log L) ^ 2 by positivity)
      nlinarith
    calc
      cost ≤ Real.exp (Cw * L * (Real.log L) ^ 2) *
          Real.exp (2 * (3 + 7 * Cm + 4 * Cj) * L * (Real.log L) ^ 2) := by
        exact mul_le_mul hWexp (hb.trans (Real.exp_le_exp.mpr hb')) (by positivity) (by positivity)
      _ = Real.exp ((K - 2) * L * (Real.log L) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [K]
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (Real.log L)])
  have hraw := high_rank_column_padding_sum P Qp F (by omega) forward j h Q D B H r M
    (L ^ (2 : ℕ)) hU hprime (zero_lt_one.trans_le hV) hmass hQmass hHN hlo hB
    hq hd hsq hpool hcount perfect cut hrank base hlit
  have htotal : (∑ a ∈ F, weight a * columnReciprocalWeight a.1 *
      ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹) ≤ cost * saving := by
    calc
      _ ≤ W * (∑ a ∈ F, columnReciprocalWeight a.1 *
          ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹) := by
        rw [mul_sum]
        apply sum_le_sum
        intro a ha
        have ha' := mul_le_mul_of_nonneg_right (hweight a ha)
          (mul_nonneg (columnReciprocalWeight_nonneg a.1) (by positivity :
            0 ≤ ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹))
        simpa only [mul_assoc] using ha'
      _ ≤ _ := by
        have hb := mul_le_mul_of_nonneg_left hraw hW
        convert hb using 1; dsimp [cost, saving]; ring
  have hm := hlogminor _ (hminor R Q D B hRL hQ hD hBexp)
  have hm' : 1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ) ≤
      Real.exp (K * Real.log L) := hm.trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hK2 (by linarith)))
  exact hdecay r (2 * R * (h * Q * D) * B) (primeHarmonicMass (P j)) H cost _
    hr.1 hr.2 hV hH hm' (by dsimp [cost]; positivity) hc htotal

end TwoPointCorrelations

end OAI
