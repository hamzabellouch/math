import OAI.NumberTheory.TwoPoint.Bounds.PaddingRetainedProbability
import OAI.NumberTheory.TwoPoint.Bounds.PaddingIntegerBins
import Mathlib.Data.Int.Interval

namespace OAI

/-! The literal finite bin family covers every padding divisor surviving
the degree and logarithmic-size cuts. This includes the last bin whose
left endpoint, rather than its right endpoint, is at most `100 L`. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def paddingBinIndices (L η : ℝ) : Finset ℤ :=
  Icc 0 ⌊100 * L / η⌋

lemma mem_paddingBinIndices_iff (L η : ℝ) (j : ℤ) (hη : 0 < η) :
    j ∈ paddingBinIndices L η ↔ 0 ≤ j ∧ (j : ℝ) * η ≤ 100 * L := by
  rw [paddingBinIndices, mem_Icc, Int.le_floor, le_div_iff₀ hη]

lemma paddingBin_mem_indices {L η x : ℝ} (hη : 0 < η)
    (hx : 0 ≤ x) (hxL : x ≤ 100 * L) :
    paddingBin η 0 x ∈ paddingBinIndices L η := by
  change ⌊(x + 0) / η⌋ ∈ Icc 0 ⌊100 * L / η⌋
  rw [add_zero, mem_Icc]
  exact ⟨Int.floor_nonneg.mpr (div_nonneg hx hη.le),
    Int.floor_mono (div_le_div_of_nonneg_right hxL hη.le)⟩

lemma paddingBinIndices_card (L η : ℝ) (hL : 0 ≤ L) (hη : 0 < η) :
    ((paddingBinIndices L η).card : ℝ) ≤ 100 * L / η + 1 := by
  have hf : 0 ≤ ⌊100 * L / η⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc : ((paddingBinIndices L η).card : ℝ) = (⌊100 * L / η⌋ : ℝ) + 1 := by
    have hh := Int.card_Icc_of_le 0 ⌊100 * L / η⌋
      (show (0 : ℤ) ≤ ⌊100 * L / η⌋ + 1 by omega)
    simp only [sub_zero] at hh
    change ((Icc (0 : ℤ) ⌊100 * L / η⌋).card : ℝ) = _
    exact_mod_cast hh
  rw [hc]
  linarith [Int.floor_le (100 * L / η)]

def PaddingPairEligible (L η : ℝ) (d q : ℕ) : Prop :=
  (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
    paddingBin η 0 (Real.log (d * q : ℕ)) ∈ paddingBinIndices L η

lemma paddingSelectedDivisor_count (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) :
    ((paddingSelectedDivisor Q b).primeFactors.card : ℝ) = booleanCount b := by
  rw [paddingSelectedDivisor_primeFactors Q hQ b, paddingAvailablePrimes_card,
    booleanCount_eq_card]
  rfl

lemma padding_pair_eligible_of_retained (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    {L η : ℝ} (hη : 0 < η) (d : ℕ) (hd : 0 < d)
    (hdL : Real.log d ≤ 2 * L) (b : Q → Bool)
    (hb : booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L) :
    PaddingPairEligible L η d (paddingSelectedDivisor Q b) := by
  refine ⟨?_, ?_⟩
  · rw [paddingSelectedDivisor_count Q hQ b]
    exact hb.1
  · apply paddingBin_mem_indices hη (log_nat_nonneg _)
    have hq : 0 < paddingSelectedDivisor Q b :=
      retainedPrimeDivisor_pos Q hQ (paddingSelectedDivisor_mem Q b)
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hq0 : (paddingSelectedDivisor Q b : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [Nat.cast_mul, Real.log_mul hd0 hq0, paddingSelectedDivisor_log Q hQ b]
    linarith [hb.2]

lemma reciprocal_padding_eligible_probability (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {L η : ℝ} (hη : 0 < η)
    (hhalf : (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
      (fun b => booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L))
    (d : ℕ) (hd : 0 < d) (hdL : Real.log d ≤ 2 * L) :
    (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
      (fun b => PaddingPairEligible L η d (paddingSelectedDivisor Q b)) := by
  apply hhalf.trans
  apply FiniteLaw.average_mono
  intro b
  by_cases hb : booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L
  · have he := padding_pair_eligible_of_retained Q hQ hη d hd hdL b hb
    simp only [ite_eq_left hb, ite_eq_left he, le_refl]
  · simp only [ite_eq_right hb]
    split_ifs <;> norm_num

theorem ModFiveThetaInput.eventually_padding_bin_probability (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ η : ℝ, 0 < η → ∀ d : ℕ,
      0 < d → Real.log d ≤ 2 * L →
      (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw (paddingPrimeSupply E L)).probability
        (fun b => PaddingPairEligible L η d
          (paddingSelectedDivisor (paddingPrimeSupply E L) b)) := by
  filter_upwards [hP.eventually_retained_padding_probability E] with L hL
  intro η hη d hd hdL
  exact reciprocal_padding_eligible_probability _ (fun _ hp => paddingPrimeSupply_prime hp)
    hη hL d hd hdL

end TwoPointCorrelations

end OAI
