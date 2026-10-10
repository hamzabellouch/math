import OAI.NumberTheory.TwoPoint.Walks.WitnessCatalogCost
import OAI.NumberTheory.TwoPoint.Bounds.SingletonDecay

namespace OAI

/-! Exponential singleton saving for the entire encoded numerical witness catalog. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_encoded_witness_decay (C Cw : ℝ) (hC : 0 ≤ C) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (R T n K M mainLength h s J H B : ℕ)
      (start len : Fin n → ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop) (W : ℝ),
      1 ≤ R → (R : ℝ) ≤ 4 * L → R ≤ M →
      (T : ℝ) ≤ C * R * Real.log L →
      (T : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      T ≤ M + 1 → n ≤ M + 1 → (n : ℝ) ≤ 4 * L → (M : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      8 * K ≤ n → L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      (∀ p ∈ P, p.Prime) → 1 ≤ primeHarmonicMass P →
      primeHarmonicMass P ≤ L ^ (2 : ℕ) → primeHarmonicMass Q ≤ L ^ (2 : ℕ) →
      1 ≤ B → (B : ℝ) ≤ Real.exp L →
      (∀ p ∈ P, H ≤ p) → (∀ p ∈ P, p ≤ B) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      W * (∑ e : PrimeWordEncoding R T P Q,
        if e.Witnesses n mainLength start len h s J supply then e.weight else 0) ≤
          Real.exp (-L ^ (21 / 20 : ℝ)) := by
  let A := 63 + Cw + 4 * (3 + 7 * C)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA2 : 2 ≤ A := by dsimp [A]; linarith
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_singleton_progression_factor, eventually_singleton_total A hA]
      with L hL hlog hfactor hdecay
  intro R T n K M mainLength h s J H B start len P Q supply W
    hR hRL hRM hslots hT hRp hTM hnM hn hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH hW hWup
  have hLp : 0 < L := by linarith
  have hHp : (0 : ℝ) < H := (Real.exp_pos _).trans_le hH
  have hHN : 0 < H := by exact_mod_cast hHp
  have hraw := encoded_witness_sum_le R T n K M mainLength h s J start len P Q supply
    hRM hsize hP hV H B hHN hB hlo hhi (hfactor B H hB hBexp hH).2
  have hcost : W * witnessCatalogCost R T n M (primeHarmonicMass P) (primeHarmonicMass Q) ≤
      Real.exp (A * L * (Real.log L) ^ 2) := by
    have hb := witnessCatalogCost_exp_bound R T n M L C hR (by linarith) hlog
      hslots hT hRp hTM hnM hn hM (primeHarmonicMass P) (primeHarmonicMass Q)
      (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity) hPup hQup
    have hr := mul_le_mul_of_nonneg_right hRL
      (show 0 ≤ (3 + 7 * C) * (Real.log L) ^ 2 by positivity)
    calc
      _ ≤ Real.exp (Cw * L * (Real.log L) ^ 2) *
          Real.exp (63 * L * (Real.log L) ^ 2 + (3 + 7 * C) * R * (Real.log L) ^ 2) :=
        mul_le_mul hWup hb (witnessCatalogCost_nonneg _ _ _ _ _ _
          (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity))
          (Real.exp_pos _).le
      _ = Real.exp (Cw * L * (Real.log L) ^ 2 +
          (63 * L * (Real.log L) ^ 2 + (3 + 7 * C) * R * (Real.log L) ^ 2)) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [A]; nlinarith)
  have hlogB : Real.log (B : ℝ) ≤ L := by
    have hb := Real.log_le_log (show (0 : ℝ) < B by exact_mod_cast (by omega : 0 < B)) hBexp
    simpa only [Real.log_exp] using hb
  have hnum : 2 + Real.log B ≤ Real.exp (A * Real.log L) := by
    have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
      rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
        Real.exp_add, Real.exp_log hLp]
      ring
    calc
      _ ≤ L ^ (2 : ℕ) := by nlinarith
      _ = Real.exp (2 * Real.log L) := he.symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA2 (by linarith))
  apply hdecay K B H (W * witnessCatalogCost R T n M (primeHarmonicMass P) (primeHarmonicMass Q))
    _ hKlo hKhi hH hnum (mul_nonneg hW (witnessCatalogCost_nonneg _ _ _ _ _ _
      (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity))) hcost
  have hb := mul_le_mul_of_nonneg_left hraw hW
  simpa only [witnessCatalogCost, mul_assoc] using hb

end TwoPointCorrelations

end OAI
