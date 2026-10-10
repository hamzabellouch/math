import OAI.NumberTheory.TwoPoint.Walks.AttachedWitnessCatalog

namespace OAI

/-! The singleton saving absorbs all record lengths, including the empty-word case. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma PrimeWordEncoding.Witnesses.length_pos {R T n mainLength h s J : ℕ}
    {P Q : Finset ℕ} {start len : Fin n → ℕ} {supply : ℕ → ℕ → Prop}
    {e : PrimeWordEncoding R T P Q}
    (he : e.Witnesses n mainLength start len h s J supply) (hn : 0 < n) : 0 < R := by
  obtain ⟨_, _, _, _, _, _, _, hminimal, _⟩ := he.2.2
  have hl := (hminimal ⟨0, hn⟩).1.1
  have ht := List.length_take_le' (len ⟨0, hn⟩) (e.decode.drop (start ⟨0, hn⟩))
  have hd : (e.decode.drop (start ⟨0, hn⟩)).length ≤ e.decode.length := by
    rw [List.length_drop]
    exact Nat.sub_le _ _
  have heLen : e.decode.length = R := e.2.1.numericalWord_length _
  have hR : 3 ≤ R := hl.trans (ht.trans (hd.trans_eq heLen))
  omega

lemma witnessLengthRecord_cost (D : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hD : (D : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (Fin (D + 1)) : ℝ) ≤ Real.exp (2 * L * (Real.log L) ^ 2) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
    rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
      Real.exp_add, Real.exp_log hLp]
    ring
  calc
    _ = (D : ℝ) + 1 := by simp
    _ ≤ L ^ (2 : ℕ) := hD
    _ = Real.exp (2 * Real.log L) := he.symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hL (sq_nonneg (Real.log L))
      nlinarith

theorem eventually_bounded_witness_decay (C Cw : ℝ) (hC : 0 ≤ C) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (D n K M h s J H B : ℕ) (slots : ℕ → ℕ)
      (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop) (W : ℝ),
      (D : ℝ) ≤ 4 * L → D ≤ M →
      (∀ R ≤ D, (slots R : ℝ) ≤ C * R * Real.log L) →
      (∀ R ≤ D, (slots R : ℝ) + 1 ≤ L ^ (2 : ℕ)) →
      (D : ℝ) + 1 ≤ L ^ (2 : ℕ) → (∀ R ≤ D, slots R ≤ M + 1) →
      0 < n → n ≤ M + 1 → (n : ℝ) ≤ 4 * L → (M : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      8 * K ≤ n → L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      (∀ p ∈ P, p.Prime) → 1 ≤ primeHarmonicMass P →
      primeHarmonicMass P ≤ L ^ (2 : ℕ) → primeHarmonicMass Q ≤ L ^ (2 : ℕ) →
      1 ≤ B → (B : ℝ) ≤ Real.exp L →
      (∀ p ∈ P, H ≤ p) → (∀ p ∈ P, p ≤ B) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ R : Fin (D + 1), ∑ d : WitnessRecord n R.val,
        W * (∑ e : PrimeWordEncoding R.val (slots R.val) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
            h s J supply then e.weight else 0)) ≤ Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_attached_witness_decay C (Cw + 2) hC (by positivity)]
      with L hL hlog hdecay
  intro D n K M h s J H B slots P Q supply W
    hD hDM hslots hslotpoly hDp hslotM hn hnM hnL hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH hW hWup
  let W' := W * (Fintype.card (Fin (D + 1)) : ℝ)
  have hW' : W' ≤ Real.exp ((Cw + 2) * L * (Real.log L) ^ 2) := by
    calc
      W' ≤ Real.exp (Cw * L * (Real.log L) ^ 2) *
          Real.exp (2 * L * (Real.log L) ^ 2) :=
        mul_le_mul hWup (witnessLengthRecord_cost D L hL hlog hDp)
          (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply sum_le_of_card_mul_le
  intro r
  have hrD : r.val ≤ D := by omega
  by_cases hr : 0 < r.val
  · have hrL : (r.val : ℝ) ≤ 4 * L :=
      (by exact_mod_cast hrD : (r.val : ℝ) ≤ D).trans hD
    have hrp : (r.val : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
      have hh : (r.val : ℝ) ≤ D := by exact_mod_cast hrD
      linarith
    have hb := hdecay r.val (slots r.val) n K M h s J H B P Q supply W'
      hr hrL (hrD.trans hDM) (hslots _ hrD) (hslotpoly _ hrD) hrp
      (hslotM _ hrD) hnM hnL hM hsize hKlo hKhi hP hV hPup hQup
      hB hBexp hlo hhi hH (by dsimp [W']; positivity) hW'
    calc
      _ = ∑ d : WitnessRecord n r.val, W' *
          (∑ e : PrimeWordEncoding r.val (slots r.val) P Q,
            if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
                (fun i => (d.1.2.2 i).val) h s J supply then e.weight else 0) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        dsimp only [W']
        ring
      _ ≤ _ := hb
  · have he (d : WitnessRecord n r.val) (e : PrimeWordEncoding r.val (slots r.val) P Q) :
        ¬e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
          (fun i => (d.1.2.2 i).val) h s J supply := fun he => hr (he.length_pos hn)
    simp only [he, ite_false, sum_const_zero, mul_zero]
    exact (Real.exp_pos _).le

end TwoPointCorrelations

end OAI
