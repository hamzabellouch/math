import OAI.Probability.SLE.Multipoint.MultipointFactorBranches
import OAI.Probability.SLE.Multipoint.MultipointDiscountedField
import OAI.Probability.SLE.Multipoint.MultipointSuccess

namespace OAI

/-! The finite branch formula for inactive, first-half, second-half, and
completed factors. Its constant part includes every completed factor. -/

noncomputable section
open Set
open scoped BigOperators

namespace SLEExactGauge.Multipoint

def phaseActive (j : Fin 4) : Prop := j = 1 ∨ j = 2

instance (j : Fin 4) : Decidable (phaseActive j) := inferInstanceAs (Decidable (_ ∨ _))

def phaseRegulatorScale (β a U : ℝ) (j : Fin 4) : ℝ :=
  if j = 1 then Real.exp (β*a) else Real.exp (-β*(U+a))

def phaseRegulatorSlope (β : ℝ) (j : Fin 4) : ℝ := if j = 1 then -β else β

def phaseWeight (κ a U : ℝ) (j : Fin 4) : ℝ :=
  if phaseActive j then factorActivationScale κ a
  else if j = 3 then Real.exp (greenExponent κ/2*U)/3 else 1

def phaseFactor (κ β a U : ℝ) (j : Fin 4) (z : ℂ × ℝ) (x : ℝ) : ℝ :=
  phaseWeight κ a U j * if phaseActive j then
    regularizedLogFactor κ (phaseRegulatorScale β a U j) (phaseRegulatorSlope β j) z x
  else 1

def patternActiveSet {ι : Type*} [Fintype ι] (j : ι → Fin 4) : Finset ι :=
  Finset.univ.filter (fun i => phaseActive (j i))

def patternWeight {ι : Type*} [Fintype ι] (κ : ℝ) (a U : ι → ℝ) (j : ι → Fin 4) : ℝ :=
  ∏ i, phaseWeight κ (a i) (U i) (j i)

def patternProduct {ι : Type*} [Fintype ι]
    (κ β : ℝ) (a U : ι → ℝ) (j : ι → Fin 4) (z : ι → ℂ × ℝ) (x : ℝ) : ℝ :=
  ∏ i, phaseFactor κ β (a i) (U i) (j i) (z i) x

def discountedPatternProduct {ι : Type*} [Fintype ι]
    (κ β : ℝ) (a U : ι → ℝ) (j : ι → Fin 4) (z : (ι → ℂ × ℝ) × ℝ) (x : ℝ) : ℝ :=
  Real.exp (-z.2)*patternProduct κ β a U j z.1 x

lemma phaseRegulatorScale_pos (β a U : ℝ) (j : Fin 4) :
    0 < phaseRegulatorScale β a U j := by
  unfold phaseRegulatorScale
  split_ifs <;> exact Real.exp_pos _

lemma phaseRegulatorSlope_le_one {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (j : Fin 4) :
    phaseRegulatorSlope β j ≤ 1 := by
  unfold phaseRegulatorSlope
  split_ifs <;> linarith

lemma phaseWeight_pos (κ a U : ℝ) (j : Fin 4) : 0 < phaseWeight κ a U j := by
  unfold phaseWeight
  split_ifs
  · exact factorActivationScale_pos κ a
  · positivity
  · norm_num

lemma phaseFactor_pos (κ β a U : ℝ) (j : Fin 4) (z : ℂ × ℝ) (x : ℝ) :
    0 < phaseFactor κ β a U j z x := by
  unfold phaseFactor
  apply mul_pos (phaseWeight_pos κ a U j)
  split_ifs
  · exact regularizedLogFactor_pos κ _ _ (phaseRegulatorScale_pos β a U j) z x
  · norm_num

lemma patternWeight_pos {ι : Type*} [Fintype ι]
    (κ : ℝ) (a U : ι → ℝ) (j : ι → Fin 4) : 0 < patternWeight κ a U j :=
  Finset.prod_pos (fun i _ => phaseWeight_pos κ (a i) (U i) (j i))

lemma patternProduct_eq {ι : Type*} [Fintype ι]
    (κ β : ℝ) (a U : ι → ℝ) (j : ι → Fin 4) (z : ι → ℂ × ℝ) (x : ℝ) :
    patternProduct κ β a U j z x = patternWeight κ a U j *
      regularizedProduct (patternActiveSet j) κ
        (fun i => phaseRegulatorScale β (a i) (U i) (j i))
        (fun i => phaseRegulatorSlope β (j i)) z x := by
  simp only [patternProduct, phaseFactor, Finset.prod_mul_distrib, patternWeight,
    regularizedProduct, patternActiveSet, Finset.prod_filter]

lemma discountedPatternProduct_eq {ι : Type*} [Fintype ι]
    (κ β : ℝ) (a U : ι → ℝ) (j : ι → Fin 4) (z : (ι → ℂ × ℝ) × ℝ) (x : ℝ) :
    discountedPatternProduct κ β a U j z x = patternWeight κ a U j *
      discountedProduct (patternActiveSet j) κ
        (fun i => phaseRegulatorScale β (a i) (U i) (j i))
        (fun i => phaseRegulatorSlope β (j i)) z x := by
  rw [discountedPatternProduct, patternProduct_eq, discountedProduct]
  ring

lemma phaseFactor_inactive (κ β a U : ℝ) (z : ℂ × ℝ) (x : ℝ) :
    phaseFactor κ β a U 0 z x = 1 := by
  norm_num [phaseFactor, phaseWeight, phaseActive]

lemma phaseFactor_first (κ β a U : ℝ) (z : ℂ × ℝ) (x : ℝ) :
    phaseFactor κ β a U 1 z x = factorActivationScale κ a *
      regularizedLogFactor κ (Real.exp (β*a)) (-β) z x := by
  norm_num [phaseFactor, phaseWeight, phaseActive, phaseRegulatorScale, phaseRegulatorSlope]

lemma phaseFactor_second (κ β a U : ℝ) (z : ℂ × ℝ) (x : ℝ) :
    phaseFactor κ β a U 2 z x = factorActivationScale κ a *
      regularizedLogFactor κ (Real.exp (-β*(U+a))) β z x := by
  norm_num [phaseFactor, phaseWeight, phaseActive, phaseRegulatorScale, phaseRegulatorSlope]

lemma phaseFactor_completed (κ β a U : ℝ) (z : ℂ × ℝ) (x : ℝ) :
    phaseFactor κ β a U 3 z x = Real.exp (greenExponent κ/2*U)/3 := by
  norm_num [phaseFactor, phaseWeight, phaseActive]

lemma phaseFactor_activation (κ β a U : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ × ℝ) (x : ℝ) (hU : 0 ≤ U) (hu : logFactorClock κ z-a = 0) :
    phaseFactor κ β a U 1 z x ≤ phaseFactor κ β a U 0 z x := by
  rw [phaseFactor_first, phaseFactor_inactive]
  exact first_branch_activation_le κ β a U hκ hκ8 z x hU hu

lemma phaseFactor_midpoint (κ β a U : ℝ) (z : ℂ × ℝ) (x : ℝ)
    (hu : logFactorClock κ z-a = U/2) :
    phaseFactor κ β a U 2 z x = phaseFactor κ β a U 1 z x := by
  rw [phaseFactor_first, phaseFactor_second, branch_midpoint_eq κ β a U z x hu]

lemma phaseFactor_completion (κ β a U : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ × ℝ) (x : ℝ) (hU : 0 ≤ U) (hu : logFactorClock κ z-a = U) :
    phaseFactor κ β a U 3 z x ≤ phaseFactor κ β a U 2 z x := by
  rw [phaseFactor_second, phaseFactor_completed]
  exact second_branch_completion_jump κ β a U hκ hκ8 z x hU hu

/-- Several coincident switches still move the factor downward. Each
crossed threshold is imposed at its actual clock value. -/
lemma phaseFactor_switch_le (κ β a U : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ × ℝ) (x : ℝ) (hU : 0 ≤ U) (j k : Fin 4) (hjk : j ≤ k)
    (hstart : j ≤ 0 → 1 ≤ k → logFactorClock κ z-a = 0)
    (hmid : j ≤ 1 → 2 ≤ k → logFactorClock κ z-a = U/2)
    (hend : j ≤ 2 → 3 ≤ k → logFactorClock κ z-a = U) :
    phaseFactor κ β a U k z x ≤ phaseFactor κ β a U j z x := by
  fin_cases j <;> fin_cases k
  all_goals norm_num at hjk
  all_goals try exact le_rfl
  · exact phaseFactor_activation κ β a U hκ hκ8 z x hU (hstart (by decide) (by decide))
  · exact (phaseFactor_midpoint κ β a U z x (hmid (by decide) (by decide))).le.trans
      (phaseFactor_activation κ β a U hκ hκ8 z x hU (hstart (by decide) (by decide)))
  · exact (phaseFactor_completion κ β a U hκ hκ8 z x hU (hend (by decide) (by decide))).trans
      ((phaseFactor_midpoint κ β a U z x (hmid (by decide) (by decide))).le.trans
        (phaseFactor_activation κ β a U hκ hκ8 z x hU (hstart (by decide) (by decide))))
  · exact (phaseFactor_midpoint κ β a U z x (hmid (by decide) (by decide))).le
  · exact (phaseFactor_completion κ β a U hκ hκ8 z x hU (hend (by decide) (by decide))).trans
      (phaseFactor_midpoint κ β a U z x (hmid (by decide) (by decide))).le
  · exact phaseFactor_completion κ β a U hκ hκ8 z x hU (hend (by decide) (by decide))

lemma patternProduct_switch_le {ι : Type*} [Fintype ι]
    (κ β : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (a U : ι → ℝ) (hU : ∀ i, 0 ≤ U i)
    (j k : ι → Fin 4) (z : ι → ℂ × ℝ) (x : ℝ) (hjk : ∀ i, j i ≤ k i)
    (hstart : ∀ i, j i ≤ 0 → 1 ≤ k i → logFactorClock κ (z i)-a i = 0)
    (hmid : ∀ i, j i ≤ 1 → 2 ≤ k i → logFactorClock κ (z i)-a i = U i/2)
    (hend : ∀ i, j i ≤ 2 → 3 ≤ k i → logFactorClock κ (z i)-a i = U i) :
    patternProduct κ β a U k z x ≤ patternProduct κ β a U j z x := by
  apply Finset.prod_le_prod₀ (fun i _ => (phaseFactor_pos κ β (a i) (U i) (k i) (z i) x).le)
  exact fun i _ => phaseFactor_switch_le κ β (a i) (U i) hκ hκ8 (z i) x
    (hU i) (j i) (k i) (hjk i) (hstart i) (hmid i) (hend i)

lemma patternProduct_all_inactive {ι : Type*} [Fintype ι]
    (κ β : ℝ) (a U : ι → ℝ) (z : ι → ℂ × ℝ) (x : ℝ) :
    patternProduct κ β a U (fun _ => 0) z x = 1 := by
  simp only [patternProduct, phaseFactor_inactive, Finset.prod_const_one]

lemma patternProduct_all_complete {ι : Type*} [Fintype ι]
    (κ β : ℝ) (a U : ι → ℝ) (z : ι → ℂ × ℝ) (x : ℝ) :
    patternProduct κ β a U (fun _ => 3) z x =
      Real.exp (greenExponent κ/2 * ∑ i, U i) / 3^(Fintype.card ι) := by
  simp only [patternProduct, phaseFactor_completed, Finset.prod_div_distrib,
    ← Real.exp_sum, Finset.prod_const, Finset.card_univ, Finset.mul_sum]

lemma discountedPatternProduct_complete_lower {ι : Type*} [Fintype ι]
    (κ β : ℝ) (a U : ι → ℝ) (z : ι → ℂ × ℝ) (b K x : ℝ) (hb : b ≤ K) :
    successBarrier (greenExponent κ) K Finset.univ U ≤
      discountedPatternProduct κ β a U (fun _ => 3) (z,b) x := by
  rw [discountedPatternProduct, patternProduct_all_complete]
  unfold successBarrier
  simp only [Finset.card_univ, zpow_neg, zpow_natCast]
  have he := Real.exp_le_exp.mpr (neg_le_neg hb)
  have hp : 0 ≤ Real.exp (greenExponent κ/2 * ∑ i, U i) / 3^Fintype.card ι := by positivity
  convert mul_le_mul_of_nonneg_right he hp using 1
  ring

end SLEExactGauge.Multipoint

end

end OAI
