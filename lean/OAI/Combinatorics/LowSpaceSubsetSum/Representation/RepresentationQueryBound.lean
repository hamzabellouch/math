import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleQueries
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketBounds

namespace OAI

/-! # Half-exponential reader-query bounds for the full representation loop -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

/-- Capacity accounting with a polynomial entry envelope. This only converts
counts: it does not assign unit time to a reader or a dictionary operation. -/
theorem prefix_tasks_polynomial {C T q m : ℕ} {u lambda x s : ℝ}
    (hu : 3 ≤ u) (hm : (m : ℝ) + 1 ≤ u)
    (hT : (C : ℝ) * T ≤ q * C + 2 * (m + 1) * (u ^ 200 * (2 : ℝ) ^ lambda))
    (hC : (2 : ℝ) ^ (s - 1) ≤ C)
    (hq : (2 : ℝ) ^ x / u ^ 2 ≤ q) (hex : lambda ≤ x + s) :
    (T : ℝ) ≤ u ^ 205 * q := by
  have hu0 : 0 < u := by linarith
  have hC0 : (0 : ℝ) < C := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hC
  have hqpow : (2 : ℝ) ^ x ≤ u ^ 2 * q := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < u ^ 2)).mp hq
    simpa only [mul_comm] using hh
  have hs : (2 : ℝ) ^ s = 2 * (2 : ℝ) ^ (s - 1) := by
    conv_lhs => rw [show s = 1 + (s - 1) by ring]
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have he : (2 : ℝ) ^ lambda ≤ (2 : ℝ) ^ x * (2 * C) := by
    calc
      _ ≤ (2 : ℝ) ^ (x + s) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hex
      _ = (2 : ℝ) ^ x * (2 * (2 : ℝ) ^ (s - 1)) := by
        rw [Real.rpow_add (by norm_num), hs]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC (by norm_num))
        (by positivity)
  have hE : u ^ 200 * (2 : ℝ) ^ lambda ≤ 2 * u ^ 202 * q * C := by
    calc
      _ ≤ u ^ 200 * ((u ^ 2 * q) * (2 * C)) := by
        exact mul_le_mul_of_nonneg_left
          (he.trans (mul_le_mul_of_nonneg_right hqpow (by positivity))) (by positivity)
      _ = _ := by ring
  have hterm : 2 * ((m : ℝ) + 1) * (u ^ 200 * (2 : ℝ) ^ lambda) ≤
      4 * u ^ 203 * q * C := by
    calc
      _ ≤ (2 * u) * (2 * u ^ 202 * q * C) :=
        mul_le_mul (by linarith) hE (by positivity) (by positivity)
      _ = _ := by ring
  have hpow : 1 + 4 * u ^ 203 ≤ u ^ 205 := by
    have hu2 : 5 ≤ u ^ 2 := by nlinarith
    have hp : 1 ≤ u ^ 203 := one_le_pow₀ (by linarith)
    have hx := mul_le_mul_of_nonneg_right hu2 (show 0 ≤ u ^ 203 by positivity)
    nlinarith only [hp, hx, show u ^ 2 * u ^ 203 = u ^ 205 by ring]
  apply (mul_le_mul_iff_right₀ hC0).mp
  calc
    (C : ℝ) * T ≤ C * ((1 + 4 * u ^ 203) * q) := by nlinarith only [hT, hterm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)

theorem reader_query_budget_polynomial {Q0 Q1 G0 G1 T0 T1 J0 J1 q m u H : ℝ}
    (hu : 3 ≤ u) (hm : m + 1 ≤ u) (hH : 0 ≤ H)
    (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hJ : 0 ≤ J0 + J1)
    (hT0 : T0 ≤ u ^ 205 * q) (hT1 : T1 ≤ u ^ 205 * q)
    (hQ0 : Q0 ≤ (6 * G0 + 2) * T0 + (m + 1) * J0)
    (hQ1 : Q1 ≤ (6 * G1 + 2) * T1 + (m + 1) * J1)
    (hG : q * (G0 + G1) ≤ u ^ 200 * H)
    (hJs : J0 + J1 ≤ u ^ 200 * H) (hq : q ≤ H) :
    Q0 + Q1 ≤ u ^ 408 * H := by
  have h0 := mul_le_mul_of_nonneg_left hT0 (show 0 ≤ 6 * G0 + 2 by linarith)
  have h1 := mul_le_mul_of_nonneg_left hT1 (show 0 ≤ 6 * G1 + 2 by linarith)
  have hJm := mul_le_mul_of_nonneg_right hm hJ
  have hsum : Q0 + Q1 ≤
      u ^ 205 * (6 * (q * (G0 + G1)) + 4 * q) + u * (J0 + J1) := by
    nlinarith only [hQ0, hQ1, h0, h1, hJm]
  have hbound : Q0 + Q1 ≤ (6 * u ^ 405 + 4 * u ^ 205 + u ^ 201) * H := by
    apply hsum.trans
    calc
      _ ≤ u ^ 205 * (6 * (u ^ 200 * H) + 4 * H) + u * (u ^ 200 * H) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by linarith only [hG, hq]) (by positivity))
          (mul_le_mul_of_nonneg_left hJs (by linarith))
      _ = _ := by ring
  have hp205 : u ^ 205 ≤ u ^ 405 := pow_le_pow_right₀ (by linarith) (by decide)
  have hp201 : u ^ 201 ≤ u ^ 405 := pow_le_pow_right₀ (by linarith) (by decide)
  have hc : 6 * u ^ 405 + 4 * u ^ 205 + u ^ 201 ≤ u ^ 408 := by
    have hu3 : 11 ≤ u ^ 3 := by
      have hsq : 9 ≤ u ^ 2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ u by linarith)
      nlinarith only [hmul, hu]
    have hmul := mul_le_mul_of_nonneg_right hu3 (show 0 ≤ u ^ 405 by positivity)
    nlinarith only [hp205, hp201, hmul, show u ^ 3 * u ^ 405 = u ^ 408 by ring]
  exact hbound.trans (mul_le_mul_of_nonneg_right hc hH)

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem resourceGamma_regeneration_exponent (z : Layout n) :
    R.extraPrimeRate z + R.resourceGamma z ≤ (n : ℝ) / 2 := by
  have hm := R.filterDeficit_mono z (by decide : (1 : Fin 3) ≤ 2)
  unfold resourceGamma
  rw [max_eq_right hm]
  exact regeneration_exponent n (mixerSize n) (binaryEntropy (1 / 4))
    (R.filterDeficit z 2) (Nat.cast_nonneg _) binaryEntropy_quarter_lt.le

variable (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 20000 ≤ n)
variable (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
variable (q : ℕ) (hq : 0 < q)

theorem schedule_taskStarts_polynomial (B : ℕ) (side : Fin 2)
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩)
    (hspread : mixerSpreadTest (R.signedWeights h.1.1.1) (R.orderedMixers h.1.1.1) n)
    (hprime : q ∈ primeRange (R.extraPrimeParameter h.1.1.1)) :
    ((∑ z : Fin q, ((R.scheduleData h r (by omega) hlog q hq).parentData side z.val).taskStarts B
      (R.scheduleData h r (by omega) hlog q hq).topOrder MaskRestriction.empty : ℕ) : ℝ) ≤
        (inputScale R.input : ℝ) ^ 205 * q := by
  have ht := R.schedule_taskStarts_sum_bound h r (by omega) hlog q hq B side
  have he := R.schedule_lowEntryUniverse_resource h r (by omega) hlog q hq hn hgood side
  have htR := (show (compressionDictionaryCapacity n : ℝ) *
      (∑ z : Fin q, ((R.scheduleData h r (by omega) hlog q hq).parentData side z.val).taskStarts B
        (R.scheduleData h r (by omega) hlog q hq).topOrder MaskRestriction.empty : ℕ) ≤
        q * compressionDictionaryCapacity n + 2 * ((mixerSize n : ℝ) + 1) *
          ((R.scheduleData h r (by omega) hlog q hq).lowEntryUniverse side).card by
    exact_mod_cast ht)
  have hbudget := htR.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left he
      (show 0 ≤ 2 * ((mixerSize n : ℝ) + 1) by positivity)))
  have hgap := R.extraPrime_entry_gap h.1.1.1 h.1.1.2 (by omega) hspread
  exact prefix_tasks_polynomial (by exact_mod_cast (show 3 ≤ inputScale R.input by
      unfold inputScale; omega))
    (by exact_mod_cast R.mixerSize_add_one_le_scale) hbudget (compression_capacity_lower n)
    (R.extraPrime_size h.1.1.1 (by omega) hprime).1 (by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith)

theorem schedule_regeneration_resource
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩)
    (hprime : q ∈ primeRange (R.extraPrimeParameter h.1.1.1)) :
    (q : ℝ) *
      (((R.scheduleData h r (by omega) hlog q hq).parentData 0 0).unrestrictedChildCount +
        ((R.scheduleData h r (by omega) hlog q hq).parentData 1 0).unrestrictedChildCount : ℝ) ≤
      (inputScale R.input : ℝ) ^ 200 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have hg := R.schedule_child_resource h r (by omega) hlog q hq hn hgood
  have hp := (R.extraPrime_size h.1.1.1 (by omega) hprime).2
  have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (R.resourceGamma_regeneration_exponent h.1.1.1)
  calc
    _ ≤ (2 : ℝ) ^ R.extraPrimeRate h.1.1.1 *
        ((inputScale R.input : ℝ) ^ 200 * (2 : ℝ) ^ R.resourceGamma h.1.1.1) :=
      mul_le_mul hp hg (by positivity) (by positivity)
    _ = (inputScale R.input : ℝ) ^ 200 *
        (2 : ℝ) ^ (R.extraPrimeRate h.1.1.1 + R.resourceGamma h.1.1.1) := by
      rw [Real.rpow_add (by norm_num)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (pow_nonneg (Nat.cast_nonneg _) 200)

/-- Proof-only total query count when early acceptance is ignored. -/
def scheduleQueries (B : ℕ) : ℕ :=
  ∑ side : Fin 2, ∑ z : Fin q,
    ((R.scheduleData h r (by omega) hlog q hq).parentData side z.val).queryVisits B
      (R.scheduleData h r (by omega) hlog q hq).topOrder MaskRestriction.empty

theorem schedule_queries_half (B : ℕ)
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩)
    (hspread : mixerSpreadTest (R.signedWeights h.1.1.1) (R.orderedMixers h.1.1.1) n)
    (hprime : q ∈ primeRange (R.extraPrimeParameter h.1.1.1)) :
    (R.scheduleQueries h r hn hlog q hq B : ℝ) ≤
      (inputScale R.input : ℝ) ^ 408 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have hT0 := R.schedule_taskStarts_polynomial h r hn hlog q hq B 0 hgood hspread hprime
  have hT1 := R.schedule_taskStarts_polynomial h r hn hlog q hq B 1 hgood hspread hprime
  have hQ0 := R.schedule_queryVisits_sum_bound h r (by omega) hlog q hq B 0
  have hQ1 := R.schedule_queryVisits_sum_bound h r (by omega) hlog q hq B 1
  have hG := R.schedule_regeneration_resource h r hn hlog q hq hgood hprime
  have hJ := R.schedule_matching_resource h r (by omega) hlog q hq hn hgood
  have hqhalf : (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
    apply (R.extraPrime_size h.1.1.1 (by omega) hprime).2.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hb := (R.extraPrimeRate_bounds h.1.1.1).2
    linarith [Nat.cast_nonneg n (α := ℝ)]
  unfold scheduleQueries
  rw [Fin.sum_univ_two, Nat.cast_add]
  let D := R.scheduleData h r (by omega) hlog q hq
  apply reader_query_budget_polynomial
    (G0 := ((D.parentData 0 0).unrestrictedChildCount : ℝ))
    (G1 := ((D.parentData 1 0).unrestrictedChildCount : ℝ))
    (J0 := ((D.lowMatchingUniverse 0).card : ℝ))
    (J1 := ((D.lowMatchingUniverse 1).card : ℝ)) (m := (mixerSize n : ℝ))
    (by exact_mod_cast (show 3 ≤ inputScale R.input by unfold inputScale; omega))
    (by exact_mod_cast R.mixerSize_add_one_le_scale) (by positivity)
    (by positivity) (by positivity) (by positivity) hT0 hT1
  · exact_mod_cast hQ0
  · exact_mod_cast hQ1
  · exact hG
  · simpa only [Nat.cast_add] using hJ
  · exact hqhalf

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
