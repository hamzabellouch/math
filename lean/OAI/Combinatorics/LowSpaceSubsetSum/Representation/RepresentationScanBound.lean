import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleUniverse
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSeparatorTrial

namespace OAI

/-! # The full schedule's separator scan budget

The sharp incidence exponent combines with the actual distinct-entry
resource budget at exponent exactly `n/2`. A single family is reused across
all buckets and prefixes; the bound uses linearity rather than independence
between checks.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem resourceLambda_separator_exponent (z : Layout n) (g : Guesses n)
    (hn : 10000 ≤ n) :
    R.resourceLambda z g + (1 - binaryEntropy (1 / 4)) * mixerSize n ≤ (n : ℝ) / 2 := by
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have hg := guess_density g hm 0
  have hp := binaryEntropy_pair_le_quarter
    (p := ((g 0).val : ℝ) / mixerSize n) (by linarith [hg.1]) (by linarith [hg.2])
  have hh : representationHbar n g ≤ binaryEntropy (1 / 4) := by
    unfold representationHbar
    linarith
  have hf : R.filterDeficit z 0 ≤
      min (deficiency R.originalWeights (R.orderedMixers z 1))
        (deficiency R.originalWeights (R.orderedMixers z 2)) := by
    apply le_min
    · have h := (R.filterDeficit_mono z (by decide : (0 : Fin 3) ≤ 1)).trans
        (min_le_right _ _)
      change R.filterDeficit z 0 ≤ deficiency R.originalWeights (R.orderedMixers z 1) / 2 at h
      linarith [deficiency_nonneg R.originalWeights (R.orderedMixers z 1)]
    · have h := (R.filterDeficit_mono z (by decide : (0 : Fin 3) ≤ 2)).trans
        (min_le_right _ _)
      change R.filterDeficit z 0 ≤ deficiency R.originalWeights (R.orderedMixers z 2) / 2 at h
      linarith [deficiency_nonneg R.originalWeights (R.orderedMixers z 2)]
  exact matching_exponent n (mixerSize n) (binaryEntropy (1 / 4))
    (representationHbar n g) _ (R.filterDeficit z 0) (Nat.cast_nonneg _) hh hf

variable (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 20000 ≤ n)
variable (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
variable (q : ℕ) (hq : 0 < q)

/-- The analysis records the actual scans of the full hypothetical loop;
early acceptance only omits a suffix of this work. -/
def scheduleScans (B : ℕ) (families : Fin 4 → Array (Finset (Fin (2 * blockHalf n 0)))) : ℕ :=
  ∑ z : Fin q, (R.topCoordinates h.1.1.1 h.1.2).totalScans families
    (R.signedTarget h.1.1.1)
    (((R.scheduleData h r (by omega) hlog q hq).bucket z.val).checkList B)

/-- On the actual low-residue resource event, all buckets together satisfy
the half-exponential scan bound. -/
theorem schedule_mean_scans_half (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩) (B : ℕ) :
    let S := separatorParameters h.1.1.2 (by omega)
    RepresentationMoments.mean (fun draws : SeparatorExpectation.IndependentFamilies
      (2 * blockHalf n 0) S.e S.counts =>
      (R.scheduleScans h r hn hlog q hq B (SeparatorExpectation.familyArrays draws) : ℝ)) ≤
      (inputScale R.input : ℝ) ^ 224 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  dsimp only
  let u : ℝ := inputScale R.input
  let W : ℝ := u ^ 200 * (2 : ℝ) ^ R.resourceLambda h.1.1.1 h.1.1.2
  have hu : (256 : ℝ) ≤ u := by
    dsimp only [u]
    exact_mod_cast (show 256 ≤ inputScale R.input by unfold inputScale; omega)
  have hmu : (mixerSize n : ℝ) + 1 ≤ u := by
    dsimp only [u]
    exact_mod_cast R.mixerSize_add_one_le_scale
  have hcoef : (2 * (mixerSize n : ℝ) + 4) ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ u by linarith)]
  have hL := R.schedule_lowEntryUniverse_resource h r (by omega) hlog q hq hn hgood 0
  have hR := R.schedule_lowEntryUniverse_resource h r (by omega) hlog q hq hn hgood 1
  have hinputs :
      ((((R.scheduleData h r (by omega) hlog q hq).lowEntryUniverse 0).card +
        (2 * mixerSize n + 3) *
        ((R.scheduleData h r (by omega) hlog q hq).lowEntryUniverse 1).card : ℕ) : ℝ) ≤
      u ^ 202 * (2 : ℝ) ^ R.resourceLambda h.1.1.1 h.1.1.2 := by
    change _ ≤ _ at hL hR
    have hW : 0 ≤ W := by dsimp only [W]; positivity
    change _ ≤ W at hL hR
    have hRscale := mul_le_mul_of_nonneg_left hR
      (show (0 : ℝ) ≤ 2 * (mixerSize n : ℝ) + 3 by positivity)
    push_cast
    calc
      _ ≤ (2 * (mixerSize n : ℝ) + 4) * W := by nlinarith
      _ ≤ u ^ 2 * W := mul_le_mul_of_nonneg_right hcoef hW
      _ = _ := by dsimp only [W]; ring
  have hnu : n ≤ inputScale R.input := by unfold inputScale; omega
  have hgu : 2 * blockHalf n 0 + 1 ≤ inputScale R.input := by
    unfold inputScale blockHalf
    simp only [Matrix.cons_val_zero]
    omega
  have hs := R.schedule_mean_allScans h r (by omega) hlog q hq B (inputScale R.input)
    (by unfold inputScale; omega) hnu hgu
  have he := R.resourceLambda_separator_exponent h.1.1.1 h.1.1.2 (by omega)
  have htop : 4 * (2 * blockHalf n 0) = mixerSize n := by
    simp [blockHalf, mixerSize]
    omega
  rw [htop] at hs
  change RepresentationMoments.mean (fun draws =>
    (R.scheduleScans h r hn hlog q hq B (SeparatorExpectation.familyArrays draws) : ℝ)) ≤ _ at hs
  apply hs.trans
  calc
    _ ≤ (u ^ 202 * (2 : ℝ) ^ R.resourceLambda h.1.1.1 h.1.1.2) * u ^ 22 *
        (2 : ℝ) ^ ((mixerSize n : ℝ) * (1 - binaryEntropy (1 / 4))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinputs (by positivity)) (by positivity)
    _ = u ^ 224 * (2 : ℝ) ^ (R.resourceLambda h.1.1.1 h.1.1.2 +
        (1 - binaryEntropy (1 / 4)) * mixerSize n) := by
      rw [Real.rpow_add (by norm_num),
        mul_comm (mixerSize n : ℝ) (1 - binaryEntropy (1 / 4))]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) he) (by positivity)

/-- A real-valued threshold for the executable integer watchdog. -/
def separatorScanBudget : ℝ :=
  (inputScale R.input : ℝ) ^ 328 * (2 : ℝ) ^ ((n : ℝ) / 2)


/-- An integer watchdog threshold computed using only multiplication and
natural exponentiation. -/
def separatorScanLimit : ℕ := inputScale R.input ^ 328 * 2 ^ ((n + 1) / 2)

theorem separatorScanBudget_le_limit :
    R.separatorScanBudget ≤ (R.separatorScanLimit : ℝ) := by
  have hn : (n : ℝ) / 2 ≤ ((n + 1) / 2 : ℕ) := by
    have h : n ≤ 2 * ((n + 1) / 2) := by omega
    have hR : (n : ℝ) ≤ 2 * ((n + 1) / 2 : ℕ) := by exact_mod_cast h
    linarith
  unfold separatorScanBudget separatorScanLimit
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    ← Real.rpow_natCast 2 ((n + 1) / 2)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hn) (by positivity)

theorem schedule_scan_tail (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩) (B : ℕ) :
    (R.separatorLaw h (by omega)).probability (fun draws =>
      R.separatorScanBudget <
        (R.scheduleScans h r hn hlog q hq B (SeparatorCheck.sampledFamilies draws) : ℝ)) ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 := by
  classical
  let S := separatorParameters h.1.1.2 (by omega)
  let (i : Fin 4) : Nonempty
      (SeparatorSample (Finset.univ : Finset (Fin (2 * blockHalf n 0))) (S.e i)) :=
    (Finset.powersetCard_nonempty.mpr (by simpa only [Finset.card_univ, Fintype.card_fin]
      using (S.size_le i))).to_subtype
  have hu : (2 : ℝ) ≤ inputScale R.input := by
    exact_mod_cast (show 2 ≤ inputScale R.input by unfold inputScale; omega)
  have hu0 : (0 : ℝ) < inputScale R.input := lt_of_lt_of_le (by norm_num) hu
  have hT : 0 < R.separatorScanBudget := by unfold separatorScanBudget; positivity
  rw [separatorLaw, FiniteLaw.uniform_probability]
  apply (RepresentationMoments.count_tail (fun draws : R.SeparatorDraws h (by omega) =>
    R.scheduleScans h r hn hlog q hq B (SeparatorCheck.sampledFamilies draws)) hT).trans
  apply (div_le_div_of_nonneg_right
    (R.schedule_mean_scans_half h r hn hlog q hq hgood B) hT.le).trans
  have hp4 : (10 : ℝ) ≤ (inputScale R.input : ℝ) ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu 4
    norm_num at hp
    linarith
  have h104 : (10 : ℝ) * (inputScale R.input : ℝ) ^ 100 ≤
      (inputScale R.input : ℝ) ^ 104 := by
    calc
      _ ≤ (inputScale R.input : ℝ) ^ 4 * (inputScale R.input : ℝ) ^ 100 :=
        mul_le_mul_of_nonneg_right hp4 (by positivity)
      _ = _ := by rw [← pow_add]
  calc
    _ = 1 / (inputScale R.input : ℝ) ^ 104 := by
      unfold separatorScanBudget
      rw [show (inputScale R.input : ℝ) ^ 328 =
        (inputScale R.input : ℝ) ^ 224 * (inputScale R.input : ℝ) ^ 104 by rw [← pow_add]]
      field_simp [ne_of_gt hu0, ne_of_gt (Real.rpow_pos_of_pos
        (by norm_num : (0 : ℝ) < 2) ((n : ℝ) / 2))]
    _ ≤ 1 / (10 * (inputScale R.input : ℝ) ^ 100) :=
      one_div_le_one_div_of_le (by positivity) h104
    _ = _ := by ring

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
