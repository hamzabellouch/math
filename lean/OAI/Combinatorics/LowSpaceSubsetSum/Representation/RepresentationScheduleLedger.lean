import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationJoinLedger
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationRuntimeFavorable

namespace OAI

/-! # Full-residue representation setup, reports, copies and controls

These counters follow the concrete parent joins and all their overflowing
prefixes. Clearing a task's workspace is included in the capacity-times-task
term. Conversion from these units to machine operations is separate.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace RepresentationScheduleData

variable {n g : ℕ} (D : RepresentationScheduleData n g)

def taskCount (B : ℕ) : ℕ :=
  ∑ side : Fin 2, ∑ z : Fin D.q,
    (D.parentData side z.val).taskStarts B D.topOrder MaskRestriction.empty

def matchingCount (B : ℕ) : ℕ :=
  ∑ side : Fin 2, ∑ z : Fin D.q,
    (D.parentData side z.val).matchingVisits B D.topOrder MaskRestriction.empty

def joinLedger (B : ℕ) : CompressionLedger :=
  ⟨∑ side : Fin 2, ∑ z : Fin D.q,
      ((D.parentData side z.val).prefixLedger B D.topOrder MaskRestriction.empty).queries,
    ∑ side : Fin 2, ∑ z : Fin D.q,
      ((D.parentData side z.val).prefixLedger B D.topOrder MaskRestriction.empty).reports,
    ∑ side : Fin 2, ∑ z : Fin D.q,
      ((D.parentData side z.val).prefixLedger B D.topOrder MaskRestriction.empty).copies,
    ∑ side : Fin 2, ∑ z : Fin D.q,
      ((D.parentData side z.val).prefixLedger B D.topOrder MaskRestriction.empty).controls⟩

theorem joinLedger_queries (B : ℕ) : (D.joinLedger B).queries = D.queryCount B := by
  simp only [joinLedger, queryCount, RepresentationParentData.prefixLedger_queries]

theorem joinLedger_bounds (B : ℕ) :
    (D.joinLedger B).reports ≤ D.matchingCount B ∧
      B * (D.joinLedger B).copies ≤ 2 * D.matchingCount B ∧
      (D.joinLedger B).controls ≤ D.queryCount B := by
  have hR := Finset.sum_le_sum (fun (side : Fin 2) (_ : side ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (z : Fin D.q) (_ : z ∈ Finset.univ) =>
      ((D.parentData side z.val).prefixLedger_bounds B D.topOrder MaskRestriction.empty).1))
  have hC := Finset.sum_le_sum (fun (side : Fin 2) (_ : side ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (z : Fin D.q) (_ : z ∈ Finset.univ) =>
      ((D.parentData side z.val).prefixLedger_bounds B D.topOrder MaskRestriction.empty).2.1))
  have hT := Finset.sum_le_sum (fun (side : Fin 2) (_ : side ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (z : Fin D.q) (_ : z ∈ Finset.univ) =>
      ((D.parentData side z.val).prefixLedger_bounds B D.topOrder MaskRestriction.empty).2.2))
  refine ⟨hR, ?_, ?_⟩
  · simpa only [joinLedger, matchingCount, Finset.mul_sum] using hC
  · simpa only [joinLedger, ← D.joinLedger_queries B] using hT

def setupUnits (B : ℕ) : ℕ := (D.capacity + 1) * D.taskCount B

def coreUnits (B : ℕ) (families : Fin 4 → Array (Finset (Fin g))) : ℕ :=
  D.setupUnits B + D.queryCount B + (D.joinLedger B).reports +
    B * (D.joinLedger B).copies + (D.joinLedger B).controls + D.scanCount B families + 1

end RepresentationScheduleData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)
variable (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 20000 ≤ n)
variable (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
variable (q : ℕ) (hq : 0 < q)

theorem schedule_matchingCount_resource (B : ℕ)
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩) :
    ((R.scheduleData h r (by omega) hlog q hq).matchingCount B : ℝ) ≤
      (inputScale R.input : ℝ) ^ 201 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  let D := R.scheduleData h r (by omega) hlog q hq
  have h0 : (∑ z : Fin q, (D.parentData 0 z.val).matchingVisits B D.topOrder MaskRestriction.empty) ≤
      (mixerSize n + 1) * (D.lowMatchingUniverse 0).card :=
    R.schedule_matchingVisits_sum_bound h r (by omega) hlog q hq B 0
  have h1 : (∑ z : Fin q, (D.parentData 1 z.val).matchingVisits B D.topOrder MaskRestriction.empty) ≤
      (mixerSize n + 1) * (D.lowMatchingUniverse 1).card :=
    R.schedule_matchingVisits_sum_bound h r (by omega) hlog q hq B 1
  have hm : D.matchingCount B ≤ (mixerSize n + 1) *
      ((D.lowMatchingUniverse 0).card + (D.lowMatchingUniverse 1).card) := by
    simp only [RepresentationScheduleData.matchingCount, Fin.sum_univ_two]
    rw [Nat.mul_add]
    convert Nat.add_le_add h0 h1 using 1
    rfl
  have hmR : (D.matchingCount B : ℝ) ≤ ((mixerSize n : ℝ) + 1) *
      (((D.lowMatchingUniverse 0).card + (D.lowMatchingUniverse 1).card : ℕ) : ℝ) := by
    exact_mod_cast hm
  have hJ := R.schedule_matching_resource h r (by omega) hlog q hq hn hgood
  have hu : (mixerSize n : ℝ) + 1 ≤ inputScale R.input := by
    exact_mod_cast R.mixerSize_add_one_le_scale
  calc
    _ ≤ ((mixerSize n : ℝ) + 1) *
        ((inputScale R.input : ℝ) ^ 200 * (2 : ℝ) ^ ((n : ℝ) / 2)) :=
      hmR.trans (mul_le_mul_of_nonneg_left hJ (by positivity))
    _ ≤ (inputScale R.input : ℝ) *
        ((inputScale R.input : ℝ) ^ 200 * (2 : ℝ) ^ ((n : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hu (mul_nonneg
        (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (by norm_num) _))
    _ = _ := by rw [← mul_assoc, ← pow_succ']

theorem extraPrime_times_capacity_half (hlarge : 100 ≤ n)
    (hprime : q ∈ primeRange (R.extraPrimeParameter h.1.1.1)) :
    (q : ℝ) * compressionDictionaryCapacity n ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have hp := (R.extraPrime_size h.1.1.1 hlarge hprime).2
  have hfloor : 1000 * (199 * n / 1000) ≤ 199 * n := by omega
  have hfloorR : (1000 : ℝ) * (199 * n / 1000 : ℕ) ≤ 199 * n := by exact_mod_cast hfloor
  have hC : (compressionDictionaryCapacity n : ℝ) ≤ (2 : ℝ) ^ ((199 / 1000 : ℝ) * n) := by
    unfold compressionDictionaryCapacity
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hfloorR])
  calc
    _ ≤ (2 : ℝ) ^ R.extraPrimeRate h.1.1.1 * (2 : ℝ) ^ ((199 / 1000 : ℝ) * n) :=
      mul_le_mul hp hC (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (R.extraPrimeRate h.1.1.1 + (199 / 1000 : ℝ) * n) :=
      (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hb := (R.extraPrimeRate_bounds h.1.1.1).2
      linarith only [hb, Nat.cast_nonneg n (α := ℝ)])

theorem schedule_setupUnits_resource (B : ℕ)
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩)
    (hspread : mixerSpreadTest (R.signedWeights h.1.1.1) (R.orderedMixers h.1.1.1) n)
    (hprime : q ∈ primeRange (R.extraPrimeParameter h.1.1.1)) :
    ((R.scheduleData h r (by omega) hlog q hq).setupUnits B : ℝ) ≤
      (inputScale R.input : ℝ) ^ 207 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  let D := R.scheduleData h r (by omega) hlog q hq
  let u : ℝ := inputScale R.input
  let C : ℝ := compressionDictionaryCapacity n
  have h0 : ((∑ z : Fin q, (D.parentData 0 z.val).taskStarts B D.topOrder MaskRestriction.empty : ℕ) : ℝ) ≤
      u ^ 205 * q := R.schedule_taskStarts_polynomial h r hn hlog q hq B 0 hgood hspread hprime
  have h1 : ((∑ z : Fin q, (D.parentData 1 z.val).taskStarts B D.topOrder MaskRestriction.empty : ℕ) : ℝ) ≤
      u ^ 205 * q := R.schedule_taskStarts_polynomial h r hn hlog q hq B 1 hgood hspread hprime
  have ht : (D.taskCount B : ℝ) ≤ 2 * u ^ 205 * q := by
    simp only [RepresentationScheduleData.taskCount, Fin.sum_univ_two, Nat.cast_add]
    calc
      _ ≤ u ^ 205 * q + u ^ 205 * q := add_le_add h0 h1
      _ = _ := by ring
  have hC : 1 ≤ C := by
    change 1 ≤ (compressionDictionaryCapacity n : ℝ)
    exact_mod_cast (show 1 ≤ compressionDictionaryCapacity n from Nat.one_le_two_pow)
  have hu : 3 ≤ u := by
    change 3 ≤ (inputScale R.input : ℝ)
    exact_mod_cast (show 3 ≤ inputScale R.input by unfold inputScale; omega)
  have hp : (q : ℝ) * C ≤ (2 : ℝ) ^ ((n : ℝ) / 2) :=
    R.extraPrime_times_capacity_half h q (by omega) hprime
  have hcoef : 4 * u ^ 205 ≤ u ^ 207 := by
    have hs : 4 ≤ u ^ 2 := by nlinarith only [hu]
    have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ u ^ 205 by positivity)
    nlinarith only [hm, show u ^ 2 * u ^ 205 = u ^ 207 by ring]
  have hcap : (D.capacity : ℝ) + 1 ≤ 2 * C := by change C + 1 ≤ _; linarith only [hC]
  calc
    _ = ((D.capacity : ℝ) + 1) * D.taskCount B := by
      simp only [RepresentationScheduleData.setupUnits, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rfl
    _ ≤ (2 * C) * (2 * u ^ 205 * q) := mul_le_mul hcap ht (by positivity) (by positivity)
    _ = (4 * u ^ 205) * ((q : ℝ) * C) := by ring
    _ ≤ u ^ 207 * (2 : ℝ) ^ ((n : ℝ) / 2) := mul_le_mul hcoef hp (by positivity) (by positivity)

/-- A favorable resource/scan history has enough slack for every charged
setup, callback, snapshot and control unit in the full residue schedule. -/
theorem schedule_coreUnits_half (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin (2 * blockHalf n 0))))
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩)
    (hspread : mixerSpreadTest (R.signedWeights h.1.1.1) (R.orderedMixers h.1.1.1) n)
    (hprime : q ∈ primeRange (R.extraPrimeParameter h.1.1.1))
    (hscan : (R.scheduleData h r (by omega) hlog q hq).scanCount B families ≤
      inputScale R.input ^ 328 * 2 ^ ((n + 1) / 2)) :
    ((R.scheduleData h r (by omega) hlog q hq).coreUnits B families : ℝ) ≤
      (inputScale R.input : ℝ) ^ 410 * (2 : ℝ) ^ ((n + 1) / 2) := by
  let D := R.scheduleData h r (by omega) hlog q hq
  let u : ℝ := inputScale R.input
  let E : ℝ := (2 : ℝ) ^ ((n + 1) / 2)
  let A : ℝ := u ^ 408 * E
  have hu : 3 ≤ u := by
    change 3 ≤ (inputScale R.input : ℝ)
    exact_mod_cast (show 3 ≤ inputScale R.input by unfold inputScale; omega)
  have hu1 : 1 ≤ u := by linarith only [hu]
  have hE : 1 ≤ E := one_le_pow₀ (by norm_num)
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu1) hE
  have hceil : (2 : ℝ) ^ ((n : ℝ) / 2) ≤ E := by
    have hc : n ≤ 2 * ((n + 1) / 2) := by omega
    have hcR : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hc
    unfold E
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hcR])
  have h201 : u ^ 201 ≤ u ^ 408 := pow_le_pow_right₀ hu1 (by decide)
  have h207 : u ^ 207 ≤ u ^ 408 := pow_le_pow_right₀ hu1 (by decide)
  have h328 : u ^ 328 ≤ u ^ 408 := pow_le_pow_right₀ hu1 (by decide)
  have hT0 := R.schedule_setupUnits_resource h r hn hlog q hq B hgood hspread hprime
  have hQ0 := R.schedule_queries_half h r hn hlog q hq B hgood hspread hprime
  have hM0 := R.schedule_matchingCount_resource h r hn hlog q hq B hgood
  have hT : (D.setupUnits B : ℝ) ≤ A :=
    hT0.trans (mul_le_mul h207 hceil (by positivity) (by positivity))
  have hQ : (D.queryCount B : ℝ) ≤ A :=
    hQ0.trans (mul_le_mul_of_nonneg_left hceil (by positivity))
  have hM : (D.matchingCount B : ℝ) ≤ A :=
    hM0.trans (mul_le_mul h201 hceil (by positivity) (by positivity))
  have hbounds := D.joinLedger_bounds B
  have hR : ((D.joinLedger B).reports : ℝ) ≤ A := by
    have hh : ((D.joinLedger B).reports : ℝ) ≤ D.matchingCount B := by exact_mod_cast hbounds.1
    exact hh.trans hM
  have hC : ((B * (D.joinLedger B).copies : ℕ) : ℝ) ≤ 2 * A := by
    have hh : ((B * (D.joinLedger B).copies : ℕ) : ℝ) ≤ 2 * (D.matchingCount B : ℝ) := by
      exact_mod_cast hbounds.2.1
    exact hh.trans (mul_le_mul_of_nonneg_left hM (by norm_num))
  have hcontrol : ((D.joinLedger B).controls : ℝ) ≤ A := by
    have hh : ((D.joinLedger B).controls : ℝ) ≤ D.queryCount B := by exact_mod_cast hbounds.2.2
    exact hh.trans hQ
  have hS : (D.scanCount B families : ℝ) ≤ A := by
    have hh : (D.scanCount B families : ℝ) ≤ u ^ 328 * E := by
      dsimp only [D, u, E]
      exact_mod_cast hscan
    exact hh.trans (mul_le_mul_of_nonneg_right h328 (by positivity))
  have hcoef : 8 * u ^ 408 ≤ u ^ 410 := by
    have hs : 8 ≤ u ^ 2 := by nlinarith only [hu]
    have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ u ^ 408 by positivity)
    nlinarith only [hm, show u ^ 2 * u ^ 408 = u ^ 410 by ring]
  calc
    (D.coreUnits B families : ℝ) ≤ 8 * A := by
      simp only [RepresentationScheduleData.coreUnits, Nat.cast_add, Nat.cast_one]
      linarith only [hT, hQ, hR, hC, hcontrol, hS, hA]
    _ = (8 * u ^ 408) * E := by unfold A; ring
    _ ≤ u ^ 410 * E := mul_le_mul_of_nonneg_right hcoef (by positivity)


end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
