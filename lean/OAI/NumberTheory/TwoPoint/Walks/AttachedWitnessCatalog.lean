import OAI.NumberTheory.TwoPoint.Walks.SegmentedWitnessDecay
import OAI.NumberTheory.TwoPoint.Bounds.RecordedWitnessSegments

namespace OAI

/-! The residue test also records the attachment positions on the main path. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

abbrev WitnessRecord (n R : ℕ) :=
  WitnessSegmentation n R × (Fin n → Fin (R + 1))

lemma witnessAttachment_cost (n R : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hn : (n : ℝ) ≤ 4 * L) (hR : (R : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (Fin n → Fin (R + 1)) : ℝ) ≤
      Real.exp (8 * L * (Real.log L) ^ 2) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
    rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
      Real.exp_add, Real.exp_log hLp]
    ring
  calc
    _ = ((R : ℝ) + 1) ^ n := by simp
    _ ≤ (L ^ (2 : ℕ)) ^ n := pow_le_pow_left₀ (by positivity) hR n
    _ = Real.exp ((n : ℝ) * (2 * Real.log L)) := by rw [Real.exp_nat_mul, he]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ 2 * Real.log L by positivity)
      have hm' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 8 * L by positivity)
      nlinarith

lemma witnessRecord_cost (n R : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hn : (n : ℝ) ≤ 4 * L) (hR : (R : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (WitnessRecord n R) : ℝ) ≤
      Real.exp (26 * L * (Real.log L) ^ 2) := by
  change (Fintype.card (WitnessSegmentation n R × (Fin n → Fin (R + 1))) : ℝ) ≤ _
  rw [Fintype.card_prod, Nat.cast_mul]
  calc
    _ ≤ Real.exp (18 * L * (Real.log L) ^ 2) *
        Real.exp (8 * L * (Real.log L) ^ 2) :=
      mul_le_mul (witnessSegmentation_cost n R L hL hlog hn hR)
        (witnessAttachment_cost n R L hL hlog hn hR) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem recorded_witness_record {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) (attachment : Fin n → ℕ)
    (hattachment : ∀ i, attachment i ≤ main.length) :
    ∃ d : WitnessRecord n (recordedWitnessWord main word).length,
      (recordedWitnessWord main word).take d.1.1.val = main ∧
      (∀ i, ((recordedWitnessWord main word).drop (d.1.2.1 i).val).take
        (d.1.2.2 i).val = word i) ∧ ∀ i, (d.2 i).val = attachment i := by
  obtain ⟨d, hd, hw⟩ := recorded_witness_segments main word
  have hmain : main.length ≤ (recordedWitnessWord main word).length := by
    simp [recordedWitnessWord]
  exact ⟨(d, fun i => ⟨attachment i, Nat.lt_succ_of_le ((hattachment i).trans hmain)⟩),
    hd, hw, fun _ => rfl⟩

theorem eventually_attached_witness_decay (C Cw : ℝ) (hC : 0 ≤ C) (hCw : 0 ≤ Cw) :
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
      (∑ d : WitnessRecord n R, W * (∑ e : PrimeWordEncoding R T P Q,
        if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
          h s J supply then e.weight else 0)) ≤
          Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_encoded_witness_decay C (Cw + 26) hC (by positivity)]
      with L hL hlog hdecay
  intro R T n K M h s J H B P Q supply W
    hR hRL hRM hslots hT hRp hTM hnM hn hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH hW hWup
  let W' := W * (Fintype.card (WitnessRecord n R) : ℝ)
  have hW' : W' ≤ Real.exp ((Cw + 26) * L * (Real.log L) ^ 2) := by
    calc
      W' ≤ Real.exp (Cw * L * (Real.log L) ^ 2) *
          Real.exp (26 * L * (Real.log L) ^ 2) :=
        mul_le_mul hWup (witnessRecord_cost n R L hL hlog hn hRp)
          (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply sum_le_of_card_mul_le
  intro d
  have hb := hdecay R T n K M d.1.1.val h s J H B
    (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val) P Q supply W'
    hR hRL hRM hslots hT hRp hTM hnM hn hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH (by dsimp [W']; positivity) hW'
  dsimp only [W'] at hb
  rw [mul_assoc, mul_left_comm W (Fintype.card (WitnessRecord n R) : ℝ)] at hb
  exact hb

end TwoPointCorrelations

end OAI
