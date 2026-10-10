import OAI.Combinatorics.ContingencyTables.Rooted.ForestPenaltyBound
import OAI.Combinatorics.ContingencyTables.Transport.PairedLabels

namespace OAI

/-!
# Adjacent actual companion weights and ideal multipliers

The parameter step is 1/(H/A). Its factor-two bounds are proved from
the literal forest penalty bound, then passed to the actual labelled
weights and their exact transversal/defect totals.
-/

namespace ContingencyTables.CompanionAnnealing

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication ForestPenaltyBound LabelledFactorial
open TwoLiftStates BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def scale (A : Instance I J) : ℝ := 10*(A.d:ℝ)^2*((A.W:ℝ)+1)

lemma scale_positive (A : Instance I J) : 0< scale A := by
  have hd : (0:ℝ)< A.d := by
    exact_mod_cast (show 0< A.d by have := A.hd; omega)
  unfold scale
  positivity

/-- The source's j*A/H parameter is exactly j/(H/A), for its literal
integer H=10*A*d²*(W+1). The arbitrary positive penalty coefficient
therefore cancels from every adjacent-phase estimate below. -/
lemma source_parameter (A : Instance I J) (coefficient j : ℕ) (hc : 0< coefficient) :
    (j:ℝ)*(coefficient:ℝ)/((10*coefficient*A.d^2*(A.W+1):ℕ):ℝ)=
      (j:ℝ)/scale A := by
  have hcR : (coefficient:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
  have hQ : scale A≠0 := (scale_positive A).ne'
  have he : ((10*coefficient*A.d^2*(A.W+1):ℕ):ℝ)=(coefficient:ℝ)*scale A := by
    unfold scale
    push_cast
    ring
  rw [he]
  field_simp [hcR,hQ]

noncomputable def weight (A : Instance I J) (j : ℕ) : Set (Labels A×Bool) → ℝ :=
  f A ((j:ℝ)/scale A)

theorem count_adjacent (A : Instance I J) (j : ℕ) (z : View A → ℕ)
    (hz : InBox (bounds A) z) :
    (1/2)*h A ((j:ℝ)/scale A) z≤ h A (((j+1:ℕ):ℝ)/scale A) z ∧
      h A (((j+1:ℕ):ℝ)/scale A) z≤ h A ((j:ℝ)/scale A) z := by
  let K (k : ℕ) (a : ForestAssignmentSplit.FreeIndex A.small A.T A.b) : ℝ :=
    (2:ℝ)^(-((k:ℝ)/scale A)*penalty A z a)
  have hterm (a : ForestAssignmentSplit.FreeIndex A.small A.T A.b) :
      (1/2)*K j a≤ K (j+1) a ∧ K (j+1) a≤ K j a := by
    have hp := penalty_bound A z hz a
    have hQ := scale_positive A
    have hPQ0 : 0≤ penalty A z a/scale A := div_nonneg hp.1 hQ.le
    have hPQ1 : penalty A z a/scale A≤1 := (div_le_one hQ).mpr hp.2
    have hlo : (1/2:ℝ)≤(2:ℝ)^(-(penalty A z a/scale A)) := by
      calc
        _ = (2:ℝ)^(-1:ℝ) := by norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hup : (2:ℝ)^(-(penalty A z a/scale A))≤1 := by
      calc
        _ ≤ (2:ℝ)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := by norm_num
    have he : K (j+1) a=K j a*(2:ℝ)^(-(penalty A z a/scale A)) := by
      unfold K
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      push_cast
      ring
    have hK : 0≤ K j a := (Real.rpow_pos_of_pos (by norm_num) _).le
    rw [he]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hlo hK]
    · nlinarith [mul_le_mul_of_nonneg_left hup hK]
  change (1/2)*(∑ a, K j a)≤(∑ a, K (j+1) a) ∧ (∑ a, K (j+1) a)≤∑ a, K j a
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => (hterm a).1)
  · exact Finset.sum_le_sum (fun a _ => (hterm a).2)

theorem weight_positive (A : Instance I J) (j : ℕ) (S : Set (Labels A×Bool)) :
    0< weight A j S := by
  exact div_pos (mul_pos (h_positive A _ _) (FactorialSignatures.factorialProduct_positive _))
    (CompanionFactorialApplication.denominator_positive A)

theorem weight_adjacent (A : Instance I J) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2)*weight A j S≤ weight A (j+1) S ∧ weight A (j+1) S≤ weight A j S := by
  have hz : InBox (bounds A) (groupCount (group (labelCell A)) S) := by
    rw [← label_capacity]
    exact SliceFactorial.groupCount_inBox _ _
  have h := count_adjacent A j _ hz
  have hc : 0≤ FactorialSignatures.factorialProduct (groupCount (group (labelCell A)) S)/
      CompanionFactorialApplication.denominator A :=
    (div_pos (FactorialSignatures.factorialProduct_positive _)
      (CompanionFactorialApplication.denominator_positive A)).le
  unfold weight f firstLift
  simp only [mul_div_assoc]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h.1 hc]
  · exact mul_le_mul_of_nonneg_right h.2 hc

theorem total_adjacent (A : Instance I J) (j : ℕ)
    (ps : List ((Labels A×Bool)×(Labels A×Bool))) (S : Set (Labels A×Bool)) :
    (1/2)*slotTotal ps (weight A j) S≤ slotTotal ps (weight A (j+1)) S ∧
      slotTotal ps (weight A (j+1)) S≤ slotTotal ps (weight A j) S := by
  constructor
  · rw [← slotTotal_scale]
    exact slotTotal_mono _ _ _ (fun T => (weight_adjacent A j T).1) _
  · exact slotTotal_mono _ _ _ (fun T => (weight_adjacent A j T).2) _

theorem ideal_adjacent (A : Instance I J) (j : ℕ)
    (p r : (Labels A×Bool)×(Labels A×Bool)) (hp : p∈pairs) (hr : r∈pairs) (hpr : p≠r) :
    (slotTotal pairs (weight A j) ∅/slotDefect pairs (weight A j) ∅ p r)/2≤
      slotTotal pairs (weight A (j+1)) ∅/slotDefect pairs (weight A (j+1)) ∅ p r ∧
    slotTotal pairs (weight A (j+1)) ∅/slotDefect pairs (weight A (j+1)) ∅ p r≤
      2*(slotTotal pairs (weight A j) ∅/slotDefect pairs (weight A j) ∅ p r) := by
  have h0 := slotTotal_pos pairs _ (weight_positive A j) ∅ PairedLabels.fresh
  have hd0 := slotDefect_pos pairs _ (weight_positive A j) ∅ PairedLabels.fresh p r hp hr hpr
  have hd1 := slotDefect_pos pairs _ (weight_positive A (j+1)) ∅ PairedLabels.fresh p r hp hr hpr
  have ha := total_adjacent A j pairs ∅
  have hb' : (1/2)*slotDefect pairs (weight A j) ∅ p r≤ slotDefect pairs (weight A (j+1)) ∅ p r ∧
      slotDefect pairs (weight A (j+1)) ∅ p r≤ slotDefect pairs (weight A j) ∅ p r := by
    unfold slotDefect
    constructor
    · rw [← slotTotal_scale]
      exact slotTotal_mono _ _ _ (fun S => (weight_adjacent A j S).1) _
    · exact slotTotal_mono _ _ _ (fun S => (weight_adjacent A j S).2) _
  constructor
  · rw [div_div,div_le_div_iff₀ (mul_pos hd0 (by norm_num)) hd1]
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hb'.2),mul_nonneg hd0.le (sub_nonneg.mpr ha.1)]
  · rw [← mul_div_assoc,div_le_div_iff₀ hd1 hd0]
    nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr ha.2),mul_nonneg h0.le (sub_nonneg.mpr hb'.1)]

end ContingencyTables.CompanionAnnealing

end OAI
