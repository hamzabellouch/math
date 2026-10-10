import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseOracleError
import OAI.Combinatorics.ContingencyTables.Transport.FiniteRationalThreshold

namespace OAI

/-! # Fresh approximate weight calls in one Metropolis acceptance decision -/

namespace ContingencyTables.CompanionOracleAcceptance

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CompanionPhaseWords CommonBasesFPRAS GridBoundary FairBits TwoLiftStates
open scoped BigOperators Classical

noncomputable section

private lemma ratio_linear_bounds {u v uh vh e : ℝ}
    (hu : 0 < u) (hv : 0 < v) (he0 : 0 ≤ e) (he1 : e ≤ 1/4)
    (huh : (1-e)*u ≤ uh ∧ uh ≤ (1+e)*u)
    (hvh : (1-e)*v ≤ vh ∧ vh ≤ (1+e)*v) :
    (1-4*e)*(v/u) ≤ vh/uh ∧ vh/uh ≤ (1+4*e)*(v/u) := by
  have huh0 := AnnealingMultipliers.empirical_positive hu he1 huh.1
  have ha0 : 0 ≤ 1-4*e := by linarith
  have hp0 : 0 ≤ 1+4*e := by linarith
  have hx : 0 < uh/u := div_pos huh0 hu
  have hlo : 1-e ≤ uh/u := (le_div_iff₀ hu).mpr huh.1
  have hhi : uh/u ≤ 1+e := (div_le_iff₀ hu).mpr huh.2
  have hyl : 1-e ≤ vh/v := (le_div_iff₀ hv).mpr hvh.1
  have hyu : vh/v ≤ 1+e := (div_le_iff₀ hv).mpr hvh.2
  have hnorm : 1-4*e ≤ (vh/v)/(uh/u) ∧ (vh/v)/(uh/u) ≤ 1+4*e := by
    constructor
    · rw [le_div_iff₀ hx]
      have hm := mul_le_mul_of_nonneg_left hhi ha0
      nlinarith [sq_nonneg e]
    · rw [div_le_iff₀ hx]
      have hm := mul_le_mul_of_nonneg_left hlo hp0
      have he : 0 ≤ 2*e-4*e^2 := by nlinarith
      nlinarith
  have hid : ((vh/v)/(uh/u))*(v/u)=vh/uh := by
    field_simp [hu.ne',hv.ne',huh0.ne']
  constructor
  · simpa only [hid] using mul_le_mul_of_nonneg_right hnorm.1 (div_pos hv hu).le
  · simpa only [hid] using mul_le_mul_of_nonneg_right hnorm.2 (div_pos hv hu).le

private lemma min_one_stability {a r s : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (h : (1-a)*r ≤ s ∧ s ≤ (1+a)*r) : |min 1 s-min 1 r| ≤ a := by
  by_cases hr : r ≤ 1 <;> by_cases hs : s ≤ 1
  · rw [min_eq_right hs,min_eq_right hr,abs_le]
    have hm := mul_nonneg ha0 (sub_nonneg.mpr hr)
    constructor <;> nlinarith
  · rw [min_eq_left (le_of_not_ge hs),min_eq_right hr,abs_le]
    have hm := mul_nonneg ha0 (sub_nonneg.mpr hr)
    constructor <;> nlinarith
  · rw [min_eq_right hs,min_eq_left (le_of_not_ge hr),abs_le]
    have hm := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr (le_of_not_ge hr))
    constructor <;> nlinarith
  · rw [min_eq_left (le_of_not_ge hs),min_eq_left (le_of_not_ge hr)]
    simpa using ha0

variable {I J : Type*} [Fintype I] [Fintype J]

def evaluatedWeight (A : Instance I J) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : Set (Labels A×Bool)) (bits : WeightWord A C K j xi) : ℚ :=
  rationalMultiplier pairs w S*evaluate A C K hK hW j xi v S bits

def targetWeight (A : Instance I J) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (S : Set (Labels A×Bool)) : ℝ :=
  (rationalMultiplier pairs w S:ℝ)*CompanionAnnealing.weight A j S

lemma targetWeight_eq (A : Instance I J) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (S : Set (Labels A×Bool)) : targetWeight A j w S=
      chainWeight pairs (fun p q => (w p q:ℝ)) (CompanionAnnealing.weight A j) S := by
  rw [targetWeight,rationalMultiplier_cast]
  rfl

lemma multiplier_positive (A : Instance I J) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S : Set (Labels A×Bool)) : 0 < rationalMultiplier pairs w S := by
  unfold rationalMultiplier
  split_ifs
  · exact hw _ _
  · norm_num

lemma targetWeight_positive (A : Instance I J) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S : Set (Labels A×Bool)) : 0 < targetWeight A j w S := by
  apply mul_pos _ (CompanionAnnealing.weight_positive A j S)
  exact_mod_cast multiplier_positive A w hw S

def acceptance (A : Instance I J) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S T : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K j xi) : ℚ :=
  min 1 (evaluatedWeight A C K j hK hW xi v w T bits.2/
    evaluatedWeight A C K j hK hW xi v w S bits.1)

def targetAcceptance (A : Instance I J) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (S T : Set (Labels A×Bool)) : ℝ := min 1 (targetWeight A j w T/targetWeight A j w S)

lemma targetAcceptance_eq (A : Instance I J) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (S T : ChainIndex (Γ := Labels A×Bool) pairs) : targetAcceptance A j w S.val T.val=
      metropolisAcceptance pairs (fun p q => (w p q:ℝ)) (CompanionAnnealing.weight A j) S T := by
  simp only [targetAcceptance,targetWeight_eq,metropolisAcceptance]

lemma evaluatedWeight_bounds (A : Instance I J) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S : Set (Labels A×Bool)) (bits : WeightWord A C K j xi)
    (hg : accurateCall A C K j hK hW xi v S bits) :
    (1-(xi:ℝ))*targetWeight A j w S ≤ (evaluatedWeight A C K j hK hW xi v w S bits:ℝ) ∧
      (evaluatedWeight A C K j hK hW xi v w S bits:ℝ) ≤ (1+(xi:ℝ))*targetWeight A j w S := by
  have hm : (0:ℝ) ≤ rationalMultiplier pairs w S := by
    exact_mod_cast (multiplier_positive A w hw S).le
  have hlo := mul_le_mul_of_nonneg_left hg.1 hm
  have hhi := mul_le_mul_of_nonneg_left hg.2 hm
  simpa only [evaluatedWeight,targetWeight,Rat.cast_mul,mul_left_comm,mul_assoc] using And.intro hlo hhi

/-- Relative errors in both weight calls cause an absolute acceptance
error at most four times the call tolerance, even across clipping at 1. -/
theorem acceptance_error (A : Instance I J) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S T : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K j xi)
    (hS : accurateCall A C K j hK hW xi v S bits.1)
    (hT : accurateCall A C K j hK hW xi v T bits.2) :
    |(acceptance A C K j hK hW xi v w S T bits:ℝ)-targetAcceptance A j w S T| ≤ 4*(xi:ℝ) := by
  have hb := ratio_linear_bounds (targetWeight_positive A j w hw S)
    (targetWeight_positive A j w hw T) (by exact_mod_cast hx0)
    (by
      have h4 : (4:ℝ)*(xi:ℝ) ≤ 1 := by
        exact_mod_cast (show (4:ℚ)*xi ≤ 1 by linarith)
      linarith)
    (evaluatedWeight_bounds A C K j hK hW xi v w hw S bits.1 hS)
    (evaluatedWeight_bounds A C K j hK hW xi v w hw T bits.2 hT)
  have hh := min_one_stability (show (0:ℝ) ≤ 4*(xi:ℝ) by exact_mod_cast mul_nonneg (by norm_num : (0:ℚ)≤4) hx0)
    (show 4*(xi:ℝ) ≤ 1 by exact_mod_cast (show 4*xi ≤ (1:ℚ) by linarith)) hb
  simpa only [acceptance,targetAcceptance,Rat.cast_min,Rat.cast_one,Rat.cast_div] using hh

lemma acceptance_bounds (A : Instance I J) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S T : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K j xi) :
    0 ≤ acceptance A C K j hK hW xi v w S T bits ∧
      acceptance A C K j hK hW xi v w S T bits ≤ 1 := by
  have hpos (X : Set (Labels A×Bool)) (b : WeightWord A C K j xi) :
      0 < evaluatedWeight A C K j hK hW xi v w X b :=
    mul_pos (multiplier_positive A w hw X)
      (evaluate_positive A C hC K hK hW hB j hj xi hx0 hx1 v X b)
  exact ⟨le_min (by norm_num) (div_pos (hpos T bits.2) (hpos S bits.1)).le,min_le_left _ _⟩

lemma targetAcceptance_bounds (A : Instance I J) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S T : Set (Labels A×Bool)) :
    0 ≤ targetAcceptance A j w S T ∧ targetAcceptance A j w S T ≤ 1 := by
  exact ⟨le_min (by norm_num)
    (div_pos (targetWeight_positive A j w hw T) (targetWeight_positive A j w hw S)).le,
    min_le_left _ _⟩

/-- This is the rounded acceptance probability of the implemented
decision, averaged over its two fresh independent weight-query words. -/
theorem average_acceptance_error (A : Instance I J) (C : ℕ) (hC : 0 < C) (K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S T : Set (Labels A×Bool)) :
    uniformAverage (fun bits : WeightWord A C K j xi × WeightWord A C K j xi =>
      |(rationalThresholdMass k (acceptance A C K j hK hW xi v w S T bits):ℝ)-
        targetAcceptance A j w S T|) ≤ 6*(xi:ℝ)+1/(2:ℝ)^k := by
  let goodS := accurateCall A C K j hK hW xi v S
  let goodT := accurateCall A C K j hK hW xi v T
  have hx1' : xi < 1 := by linarith
  have hbad : uniformAverage (fun bits : WeightWord A C K j xi × WeightWord A C K j xi =>
      if ¬(goodS bits.1 ∧ goodT bits.2) then (1:ℝ) else 0) ≤ (xi:ℝ)+(xi:ℝ) := by
    have hs := accurateCall_failure A C hC K j hK hW hB hj xi hx0 hx1' hPL hCheeger v S
    have ht := accurateCall_failure A C hC K j hK hW hB hj xi hx0 hx1' hPL hCheeger v T
    exact @independent_pair_failure (WeightWord A C K j xi) (WeightWord A C K j xi)
      inferInstance inferInstance inferInstance inferInstance goodS goodT (xi:ℝ) (xi:ℝ) hs ht
  have hpoint (bits : WeightWord A C K j xi × WeightWord A C K j xi) :
      |(rationalThresholdMass k (acceptance A C K j hK hW xi v w S T bits):ℝ)-targetAcceptance A j w S T| ≤
        (4*(xi:ℝ)+1/(2:ℝ)^k)+(if ¬(goodS bits.1 ∧ goodT bits.2) then 1 else 0) := by
    let q := acceptance A C K j hK hW xi v w S T bits
    have hq := acceptance_bounds A C hC K j hK hW hB hj xi hx0 hx1' v w hw S T bits
    have hr := rationalThreshold_error k q hq.1
    have hnon : (0:ℝ) ≤ (q:ℝ)-(rationalThresholdMass k q:ℝ) := by exact_mod_cast sub_nonneg.mpr hr.2.1
    have hround : |(rationalThresholdMass k q:ℝ)-(q:ℝ)| ≤ 1/(2:ℝ)^k := by
      rw [abs_sub_comm,abs_of_nonneg hnon]
      have hc : ((q-rationalThresholdMass k q:ℚ):ℝ) ≤ ((1/(2:ℚ)^k:ℚ):ℝ) :=
        Rat.cast_le.mpr hr.2.2.le
      simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hc
    have htriangle := abs_add_le ((rationalThresholdMass k q:ℝ)-(q:ℝ))
      ((q:ℝ)-targetAcceptance A j w S T)
    have hcancel : (rationalThresholdMass k q:ℝ)-(q:ℝ)+((q:ℝ)-targetAcceptance A j w S T)=
        (rationalThresholdMass k q:ℝ)-targetAcceptance A j w S T := by ring
    rw [hcancel] at htriangle
    by_cases hg : goodS bits.1 ∧ goodT bits.2
    · have herr := acceptance_error A C K j hK hW xi hx0.le hx1 v w hw S T bits hg.1 hg.2
      simpa [q,hg,add_comm] using htriangle.trans (add_le_add hround herr)
    · have ht := targetAcceptance_bounds A j w hw S T
      have hdiff : |(q:ℝ)-targetAcceptance A j w S T| ≤ 1 := by
        have hqR : (0:ℝ) ≤ q ∧ (q:ℝ) ≤ 1 := by exact_mod_cast hq
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      simp only [hg,not_false_eq_true,ite_true]
      have hxR : (0:ℝ) ≤ xi := by exact_mod_cast hx0.le
      linarith [htriangle]
  have hh := uniformAverage_mono _ _ hpoint
  rw [uniformAverage_add,uniformAverage_const] at hh
  linarith

end

end ContingencyTables.CompanionOracleAcceptance

end OAI
