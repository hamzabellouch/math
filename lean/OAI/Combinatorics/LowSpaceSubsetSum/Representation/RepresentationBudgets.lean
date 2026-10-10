import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationAllocatedEntries

namespace OAI

/-! # Concrete ambient resource budgets, including integer prime exponents -/

noncomputable section

namespace LowSpaceSubsetSum

open RepresentationSetup

def representationHbar (n : ℕ) (g : Guesses n) : ℝ :=
  (binaryEntropy (((g 0).val : ℝ) / mixerSize n) +
    binaryEntropy (1 / 2 - ((g 0).val : ℝ) / mixerSize n)) / 2

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def filterDeficit (z : Layout n) (i : Fin 3) : ℝ :=
  min ((39 / 5000 : ℝ) * n) (deficiency R.originalWeights (R.orderedMixers z i) / 2)

def resourceGamma (z : Layout n) : ℝ :=
  pairExponent n (mixerSize n) (binaryEntropy (1 / 4))
    (max (R.filterDeficit z 1) (R.filterDeficit z 2))

def resourceLambda (z : Layout n) (g : Guesses n) : ℝ :=
  entryExponent n (mixerSize n) (representationHbar n g)
    (min (deficiency R.originalWeights (R.orderedMixers z 1))
      (deficiency R.originalWeights (R.orderedMixers z 2))) (R.filterDeficit z 0)

theorem lowExponent_eq_half_sub (z : Layout n) (i : Fin 3) :
    R.lowExponent z i = (mixerSize n : ℝ) / 2 - R.filterDeficit z i := by
  have hs : 2 * R.halfSize = mixerSize n := by rw [R.halfSize_eq]; unfold mixerSize; omega
  have hsR : (2 : ℝ) * R.halfSize = mixerSize n := by exact_mod_cast hs
  unfold lowExponent filterDeficit
  linarith

theorem floor_lowExponent_lower (z : Layout n) (i : Fin 3) :
    R.lowExponent z i - 1 ≤ (⌊R.lowExponent z i⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one (R.lowExponent z i)
  linarith

theorem filterDeficit_le_tau (z : Layout n) (i : Fin 3) :
    R.filterDeficit z i ≤ (39 / 5000 : ℝ) * n := min_le_left _ _

theorem local_filterDeficit_le_max (z : Layout n) (j : Fin 2) :
    R.filterDeficit z j.succ ≤ max (R.filterDeficit z 1) (R.filterDeficit z 2) := by
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem beta_sub_floor_lowExponent (z : Layout n) (g : Guesses n) (hn : 400 ≤ n)
    (j : Fin 2) :
    representationBeta n g j - (⌊R.lowExponent z j.succ⌋₊ : ℝ) ≤ R.resourceGamma z + 1 := by
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have hb := representationBeta_upper g hm j
  have hf := R.floor_lowExponent_lower z j.succ
  have he := R.lowExponent_eq_half_sub z j.succ
  have hmax := R.local_filterDeficit_le_max z j
  unfold resourceGamma pairExponent
  linarith

/-- The strict tuple slack absorbs both losses from flooring low exponents. -/
theorem twice_beta_sub_floor_lowExponents (z : Layout n) (g : Guesses n)
    (hn : 20000 ≤ n) (j : Fin 2) :
    2 * representationBeta n g j - (⌊R.lowExponent z 0⌋₊ : ℝ) -
      (⌊R.lowExponent z j.succ⌋₊ : ℝ) ≤ (n : ℝ) / 2 := by
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have hb := representationBeta_upper g hm j
  have hf0 := R.floor_lowExponent_lower z 0
  have hfj := R.floor_lowExponent_lower z j.succ
  have he0 := R.lowExponent_eq_half_sub z 0
  have hej := R.lowExponent_eq_half_sub z j.succ
  have hd0 := R.filterDeficit_le_tau z 0
  have hdj := R.filterDeficit_le_tau z j.succ
  have hmul := mul_le_mul_of_nonneg_right binaryEntropy_quarter_lt.le
    (Nat.cast_nonneg (mixerSize n) (α := ℝ))
  have hmbound := (mixerSize_bounds n).1.le
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

end RepresentationSetup

namespace RepresentationMoments

/-- A one-bit loss in each child exponent is absorbed by the polynomial factor
in the input scale, while preserving the exact exponential rate. -/
theorem pair_budget_with_floor {ι : Type*} (L R : Fin 4 → RepresentationLeaf ι)
    {u betaL betaR ellL ellR pL pR gamma : ℝ} (hu : 8 ≤ u)
    (hpL : 0 < pL) (hpR : 0 < pR)
    (hL : ∀ i, ((L i).occurrences.card : ℝ) ≤ u ^ 10 * (2 : ℝ) ^ (betaL / 2))
    (hR : ∀ i, ((R i).occurrences.card : ℝ) ≤ u ^ 10 * (2 : ℝ) ^ (betaR / 2))
    (hmL : (2 : ℝ) ^ ellL / u ^ 5 ≤ pL) (hmR : (2 : ℝ) ^ ellR / u ^ 5 ≤ pR)
    (hgL : betaL - ellL ≤ gamma + 1) (hgR : betaR - ellR ≤ gamma + 1) :
    ((RepresentationUniverse.children L 0).card + (RepresentationUniverse.children L 1).card : ℝ) / pL +
      ((RepresentationUniverse.children R 0).card + (RepresentationUniverse.children R 1).card : ℝ) / pR ≤
        u ^ 26 * (2 : ℝ) ^ gamma := by
  have hu0 : 0 < u := by linarith
  have hpow : (2 : ℝ) ^ (gamma + 1) = 2 * (2 : ℝ) ^ gamma := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
    ring
  have hl (j : Fin 2) := (divide_by_modulus hu0 hpL 20
    (child_card_bound L hu0.le hL j) hmL).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hgL)
        (by positivity : 0 ≤ u ^ 25))
  have hr (j : Fin 2) := (divide_by_modulus hu0 hpR 20
    (child_card_bound R hu0.le hR j) hmR).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hgR)
        (by positivity : 0 ≤ u ^ 25))
  simp only [hpow] at hl hr
  rw [add_div, add_div]
  calc
    _ ≤ 8 * (u ^ 25 * (2 : ℝ) ^ gamma) := by linarith [hl 0, hl 1, hr 0, hr 1]
    _ ≤ u * (u ^ 25 * (2 : ℝ) ^ gamma) := mul_le_mul_of_nonneg_right hu (by positivity)
    _ = _ := by rw [show 26 = 25 + 1 by decide, pow_succ]; ring

end RepresentationMoments

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem entry_exponent_with_floor (z : Layout n) (g : Guesses n)
    {u : ℝ} (hu : 2 ≤ u) (hmu : (mixerSize n : ℝ) + 1 ≤ u) (j : Fin 2) :
    (representationBackgroundSize n : ℝ) / 2 +
      (representationEntropy n g false 0 + representationEntropy n g true 0) / 2 +
      (mixerSize n : ℝ) - deficiency (R.signedWeights z) (R.orderedMixers z j.succ) +
      Real.logb 2 ((mixerSize n : ℝ) + 1) + 2 ≤
        R.resourceLambda z g + (⌊R.lowExponent z 0⌋₊ : ℝ) + Real.logb 2 (u ^ 5) := by
  have hsigned : deficiency (R.signedWeights z) (R.orderedMixers z j.succ) =
      deficiency R.originalWeights (R.orderedMixers z j.succ) := by
    rw [signedWeights, deficiency_flip]
  have hdmin : min (deficiency R.originalWeights (R.orderedMixers z 1))
      (deficiency R.originalWeights (R.orderedMixers z 2)) ≤
      deficiency R.originalWeights (R.orderedMixers z j.succ) := by
    fin_cases j
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hA : (representationEntropy n g false 0 + representationEntropy n g true 0) / 2 =
      (mixerSize n : ℝ) * representationHbar n g := by
    simp only [representationEntropy, orientedDensity, Bool.false_eq_true, ↓reduceIte,
      representationHbar]
    ring
  have hf := R.floor_lowExponent_lower z 0
  have he := R.lowExponent_eq_half_sub z 0
  have hlog1 : 1 ≤ Real.logb 2 u := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hu
  have hlogm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (mixerSize n : ℝ) + 1) hmu
  have hlogExtra : Real.logb 2 ((mixerSize n : ℝ) + 1) + 3 ≤ Real.logb 2 (u ^ 5) := by
    rw [Real.logb_pow]
    norm_num
    linarith
  rw [hsigned, hA, representationBackgroundSize_cast]
  unfold resourceLambda entryExponent
  linarith

theorem allocated_entry_budget (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    {u p0 : ℝ} (hu : 2 ≤ u) (hmu : (mixerSize n : ℝ) + 1 ≤ u) (hp0 : 0 < p0)
    (hm0 : (2 : ℝ) ^ (⌊R.lowExponent z 0⌋₊ : ℝ) / u ^ 5 ≤ p0) (j : Fin 2) :
    ((RepresentationUniverse.validEntries (R.signedWeights z)
      (R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j)).card : ℝ) / p0 ≤
      u ^ 10 * (2 : ℝ) ^ R.resourceLambda z g := by
  have hu0 : 0 < u := by linarith
  have hexp := R.entry_exponent_with_floor z g hu hmu j
  have hcard : ((RepresentationUniverse.validEntries (R.signedWeights z)
      (R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j)).card : ℝ) ≤
      u ^ 5 * (2 : ℝ) ^ (R.resourceLambda z g + (⌊R.lowExponent z 0⌋₊ : ℝ)) := by
    apply (R.rawLeaf_allocated_entry_card_bound z g f hn hlog j).trans
    calc
      _ ≤ (2 : ℝ) ^ (R.resourceLambda z g + (⌊R.lowExponent z 0⌋₊ : ℝ) +
          Real.logb 2 (u ^ 5)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = _ := by
        rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
        ring
  have hb := RepresentationMoments.divide_by_modulus hu0 hp0 5 hcard hm0
  simpa only [Nat.reduceAdd, add_sub_cancel_right] using hb

theorem allocated_resource_failure {p0 pL pR : ℕ}
    (hp0 : 0 < p0) (hpL : 0 < pL) (hpR : 0 < pR)
    (z : Layout n) (g : Guesses n) (f : R.Partitions z) (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    {u : ℝ} (hu : 8 ≤ u) (hmu : (mixerSize n : ℝ) + 1 ≤ u)
    (hm0 : (2 : ℝ) ^ (⌊R.lowExponent z 0⌋₊ : ℝ) / u ^ 5 ≤ p0)
    (hmL : (2 : ℝ) ^ (⌊R.lowExponent z 1⌋₊ : ℝ) / u ^ 5 ≤ pL)
    (hmR : (2 : ℝ) ^ (⌊R.lowExponent z 2⌋₊ : ℝ) / u ^ 5 ≤ pR) :
    let B := R.allocatedBackground z g (by omega) hlog
    finiteUniformProbability (fun r : RepresentationMoments.Residues p0 pL pR =>
      ¬RepresentationMoments.GoodResource hp0 hpL hpR (R.signedWeights z)
        (R.rawLeaf z g f B 0) (R.rawLeaf z g f B 1) (R.signedTarget z)
        u (R.resourceGamma z) (R.resourceLambda z g) ((n : ℝ) / 2) r) <
      (1 / 10 : ℝ) / u ^ 100 := by
  let B := R.allocatedBackground z g (by omega) hlog
  have hu2 : 2 ≤ u := by linarith
  have hLeaf (j : Fin 2) (i : Fin 4) := R.rawLeaf_allocated_card z g f (by omega) hlog hu2 hmu j i
  have hpos0 : (0 : ℝ) < p0 := by exact_mod_cast hp0
  have hposL : (0 : ℝ) < pL := by exact_mod_cast hpL
  have hposR : (0 : ℝ) < pR := by exact_mod_cast hpR
  have hG := RepresentationMoments.pair_budget_with_floor
    (R.rawLeaf z g f B 0) (R.rawLeaf z g f B 1) hu hposL hposR
    (hLeaf 0) (hLeaf 1) hmL hmR
    (R.beta_sub_floor_lowExponent z g (by omega) 0)
    (R.beta_sub_floor_lowExponent z g (by omega) 1)
  have hJ := RepresentationMoments.tuple_budget
    (R.rawLeaf z g f B 0) (R.rawLeaf z g f B 1) hu2 hpos0 hposL hposR
    (hLeaf 0) (hLeaf 1) hm0 hmL hmR
    (R.twice_beta_sub_floor_lowExponents z g hn 0)
    (R.twice_beta_sub_floor_lowExponents z g hn 1)
  have hUL := R.allocated_entry_budget z g f (by omega) hlog hu2 hmu hpos0 hm0 0
  have hUR := R.allocated_entry_budget z g f (by omega) hlog hu2 hmu hpos0 hm0 1
  have hJ' : ((RepresentationUniverse.parents (R.rawLeaf z g f B 0)).card : ℝ) /
      (p0 * pL : ℕ) + ((RepresentationUniverse.parents (R.rawLeaf z g f B 1)).card : ℝ) /
      (p0 * pR : ℕ) ≤ u ^ 51 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
    simpa only [Nat.cast_mul] using hJ
  exact (RepresentationMoments.resource_failure_le hp0 hpL hpR (R.signedWeights z)
    (R.rawLeaf z g f B 0) (R.rawLeaf z g f B 1) (R.signedTarget z)
    u (R.resourceGamma z) (R.resourceLambda z g) ((n : ℝ) / 2) (by linarith)
    hG hJ' hUL hUR).trans_lt (RepresentationMoments.resource_failure_small hu2)

end RepresentationSetup

end LowSpaceSubsetSum

end

end OAI
