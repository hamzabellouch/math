import OAI.Combinatorics.ContingencyTables.Rooted.RootedScaledBounds
import OAI.Combinatorics.ContingencyTables.Rooted.RootedFactorialApplication
import OAI.Combinatorics.ContingencyTables.Counting.CompanionAnnealing

namespace OAI

/-!
# Adjacent selected-root weights and ideal multipliers

The actual computed-root penalty satisfies the source height bound.
It gives the factor-two annealing estimates for the same literal
completion count used by the executed density evaluator.
-/

namespace ContingencyTables.RootedAnnealing

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial
open CompanionAnnealing (scale scale_positive source_parameter)
open ForestAssignmentSplit
open ForestScaledPenalty (rowCounts columnCounts integerCube)
open TwoLiftStates BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The selected-root penalty of an actual integer free assignment. -/
noncomputable def penalty (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) : ℝ :=
  RootedLiteralCount.actualPenalty A R
    (ForestCountIdentification.smallX A.small z) (ForestCountIdentification.smallY A.small z)
    (freeTable A.small A.T A.b f)
    (RootedPhysicalCompletion.solved A R (rowCounts A z) (columnCounts A z)
      (fun i j => (freeTable A.small A.T A.b f i j:ℤ)))

/-- The source height bound holds for the selected, computed root too. -/
theorem penalty_bound (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (z : View A → ℕ) (hz : InBox (bounds A) z)
    (f : FreeIndex A.small A.T A.b) :
    0≤ penalty A R z f ∧ penalty A R z f≤ scale A := by
  have hv (a : FreeCell A.small A.T) :
      0≤ integerCube A 1 f a ∧ integerCube A 1 f a≤1 := by
    have hp : (0:ℝ)<(A.b a.val.1 a.val.2:ℝ)+1 := by positivity
    have hf : ((f a).val:ℝ)≤(A.b a.val.1 a.val.2:ℝ)+1 := by
      exact_mod_cast (Nat.le_of_lt (f a).isLt)
    unfold integerCube
    simp only [one_mul]
    exact ⟨div_nonneg (Nat.cast_nonneg _) hp.le,(div_le_one hp).mpr hf⟩
  have hb := RootedScaledPenalty.penalty_cube_bound A R 1 1
    (by norm_num) (by norm_num) z hz (integerCube A 1 f) hv
  have he := RootedScaledPenalty.penalty_at_integer A R 1 1 (by norm_num) z f
  have hr : (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))=rowCounts A z := rfl
  have hc : (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))=
      columnCounts A z := rfl
  rw [hr,hc] at he
  rw [he] at hb
  simpa only [one_mul,penalty,scale] using hb

noncomputable def weight (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) : Set (Labels A×Bool) → ℝ :=
  RootedFactorialApplication.f A R ((j:ℝ)/scale A)

theorem count_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (z : View A → ℕ)
    (hz : InBox (bounds A) z) :
    (1/2)*RootedCountIdentification.h A R ((j:ℝ)/scale A) z≤ RootedCountIdentification.h A R (((j+1:ℕ):ℝ)/scale A) z ∧
      RootedCountIdentification.h A R (((j+1:ℕ):ℝ)/scale A) z≤ RootedCountIdentification.h A R ((j:ℝ)/scale A) z := by
  let K (k : ℕ) (a : ForestAssignmentSplit.FreeIndex A.small A.T A.b) : ℝ :=
    (2:ℝ)^(-((k:ℝ)/scale A)*penalty A R z a)
  have hterm (a : ForestAssignmentSplit.FreeIndex A.small A.T A.b) :
      (1/2)*K j a≤ K (j+1) a ∧ K (j+1) a≤ K j a := by
    have hp := penalty_bound A R z hz a
    have hQ := scale_positive A
    have hPQ0 : 0≤ penalty A R z a/scale A := div_nonneg hp.1 hQ.le
    have hPQ1 : penalty A R z a/scale A≤1 := (div_le_one hQ).mpr hp.2
    have hlo : (1/2:ℝ)≤(2:ℝ)^(-(penalty A R z a/scale A)) := by
      calc
        _ = (2:ℝ)^(-1:ℝ) := by norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hup : (2:ℝ)^(-(penalty A R z a/scale A))≤1 := by
      calc
        _ ≤ (2:ℝ)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := by norm_num
    have he : K (j+1) a=K j a*(2:ℝ)^(-(penalty A R z a/scale A)) := by
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

theorem weight_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    0< weight A R j S := by
  exact div_pos (mul_pos (RootedCountIdentification.h_positive A R _ _) (FactorialSignatures.factorialProduct_positive _))
    (CompanionFactorialApplication.denominator_positive A)

theorem weight_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2)*weight A R j S≤ weight A R (j+1) S ∧ weight A R (j+1) S≤ weight A R j S := by
  have hz : InBox (bounds A) (groupCount (group (labelCell A)) S) := by
    rw [← label_capacity]
    exact SliceFactorial.groupCount_inBox _ _
  have h := count_adjacent A R j _ hz
  have hc : 0≤ FactorialSignatures.factorialProduct (groupCount (group (labelCell A)) S)/
      CompanionFactorialApplication.denominator A :=
    (div_pos (FactorialSignatures.factorialProduct_positive _)
      (CompanionFactorialApplication.denominator_positive A)).le
  unfold weight RootedFactorialApplication.f firstLift
  simp only [mul_div_assoc]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h.1 hc]
  · exact mul_le_mul_of_nonneg_right h.2 hc

theorem total_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (ps : List ((Labels A×Bool)×(Labels A×Bool))) (S : Set (Labels A×Bool)) :
    (1/2)*slotTotal ps (weight A R j) S≤ slotTotal ps (weight A R (j+1)) S ∧
      slotTotal ps (weight A R (j+1)) S≤ slotTotal ps (weight A R j) S := by
  constructor
  · rw [← slotTotal_scale]
    exact slotTotal_mono _ _ _ (fun T => (weight_adjacent A R j T).1) _
  · exact slotTotal_mono _ _ _ (fun T => (weight_adjacent A R j T).2) _

theorem ideal_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (p r : (Labels A×Bool)×(Labels A×Bool)) (hp : p∈pairs) (hr : r∈pairs) (hpr : p≠r) :
    (slotTotal pairs (weight A R j) ∅/slotDefect pairs (weight A R j) ∅ p r)/2≤
      slotTotal pairs (weight A R (j+1)) ∅/slotDefect pairs (weight A R (j+1)) ∅ p r ∧
    slotTotal pairs (weight A R (j+1)) ∅/slotDefect pairs (weight A R (j+1)) ∅ p r≤
      2*(slotTotal pairs (weight A R j) ∅/slotDefect pairs (weight A R j) ∅ p r) := by
  have h0 := slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh
  have hd0 := slotDefect_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh p r hp hr hpr
  have hd1 := slotDefect_pos pairs _ (weight_positive A R (j+1)) ∅ PairedLabels.fresh p r hp hr hpr
  have ha := total_adjacent A R j pairs ∅
  have hb' : (1/2)*slotDefect pairs (weight A R j) ∅ p r≤ slotDefect pairs (weight A R (j+1)) ∅ p r ∧
      slotDefect pairs (weight A R (j+1)) ∅ p r≤ slotDefect pairs (weight A R j) ∅ p r := by
    unfold slotDefect
    constructor
    · rw [← slotTotal_scale]
      exact slotTotal_mono _ _ _ (fun S => (weight_adjacent A R j S).1) _
    · exact slotTotal_mono _ _ _ (fun S => (weight_adjacent A R j S).2) _
  constructor
  · rw [div_div,div_le_div_iff₀ (mul_pos hd0 (by norm_num)) hd1]
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hb'.2),mul_nonneg hd0.le (sub_nonneg.mpr ha.1)]
  · rw [← mul_div_assoc,div_le_div_iff₀ hd1 hd0]
    nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr ha.2),mul_nonneg h0.le (sub_nonneg.mpr hb'.1)]

end ContingencyTables.RootedAnnealing

end OAI
