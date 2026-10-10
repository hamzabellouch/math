import OAI.NumberTheory.TwoPoint.Bounds.EncodedWitnessDecay
import OAI.NumberTheory.TwoPoint.Walks.WitnessSegmentation

namespace OAI

/-! Include every main/witness segment record in the singleton decay estimate. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_segmented_witness_decay (C Cw : ℝ) (hC : 0 ≤ C) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (R T n K M h s J H B : ℕ)
      (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop) (W : ℝ),
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
      (∑ d : WitnessSegmentation n R, W * (∑ e : PrimeWordEncoding R T P Q,
        if e.Witnesses n d.1.val (fun i => (d.2.1 i).val) (fun i => (d.2.2 i).val)
          h s J supply then e.weight else 0)) ≤
          Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_encoded_witness_decay C (Cw + 18) hC (by positivity)]
      with L hL hlog hdecay
  intro R T n K M h s J H B P Q supply W
    hR hRL hRM hslots hT hRp hTM hnM hn hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH hW hWup
  let W' := W * (Fintype.card (WitnessSegmentation n R) : ℝ)
  have hW' : W' ≤ Real.exp ((Cw + 18) * L * (Real.log L) ^ 2) := by
    calc
      W' ≤ Real.exp (Cw * L * (Real.log L) ^ 2) *
          Real.exp (18 * L * (Real.log L) ^ 2) :=
        mul_le_mul hWup (witnessSegmentation_cost n R L hL hlog hn hRp)
          (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply sum_le_of_card_mul_le
  intro d
  have hb := hdecay R T n K M d.1.val h s J H B
    (fun i => (d.2.1 i).val) (fun i => (d.2.2 i).val) P Q supply W'
    hR hRL hRM hslots hT hRp hTM hnM hn hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH (by dsimp [W']; positivity) hW'
  dsimp only [W'] at hb
  rw [mul_assoc, mul_left_comm W (Fintype.card (WitnessSegmentation n R) : ℝ)] at hb
  exact hb

end TwoPointCorrelations

end OAI
