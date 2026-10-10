import OAI.Combinatorics.ContingencyTables.Counting.CompanionAnnealing
import OAI.Combinatorics.ContingencyTables.Counting.AnnealingMultipliers

namespace OAI

/-!
# Actual companion empirical multiplier and counting updates

The observables and empirical counts are those of the actual labelled
chain. The update cancels the preceding multiplier, and the next-parameter
comparison is derived from the literal bounded forest penalty.
-/

namespace ContingencyTables.CompanionMultiplierUpdate

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def ratio (A : Instance I J) (j : ℕ) (S : Set (Labels A×Bool)) : ℝ :=
  weight A (j+1) S/weight A j S

lemma ratio_bounds (A : Instance I J) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2:ℝ)≤ ratio A j S ∧ ratio A j S≤1 := by
  have h := weight_adjacent A j S
  unfold ratio
  constructor
  · exact (le_div_iff₀ (weight_positive A j S)).mpr h.1
  · exact (div_le_one (weight_positive A j S)).mpr h.2

lemma ratio_mean (A : Instance I J) (j : ℕ)
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ) :
    chainMean pairs w (weight A j) (plainObservable pairs (ratio A j))=
      slotTotal pairs (weight A (j+1)) ∅/chainTotal pairs w (weight A j) := by
  rw [plainObservable_mean pairs PairedLabels.fresh PairedLabels.cover]
  congr 2
  funext S
  unfold ratio
  exact mul_div_cancel₀ _ (weight_positive A j S).ne'

/-- The explicit observed-type-count update gives good multipliers for
j+1. Its only statistical hypothesis is relative accuracy of the actual
finite observations at phase j. -/
theorem successful_phase_learns (A : Instance I J) (j : ℕ)
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0< w p r) (eta : ℝ) (he0 : 0≤ eta) (he : eta≤1/4)
    (l : List (Set (Labels A×Bool)))
    (hacc : AccuratePhase pairs w (weight A j) (ratio A j) eta l) :
    GoodMultipliers pairs (weight A (j+1)) (learnedMultipliers pairs w l) := by
  have hZ := chainTotal_pos pairs PairedLabels.fresh PairedLabels.cover w
    (weight A j) (weight_positive A j) hw
  have hp0 : 0< chainMean pairs w (weight A j) (plainObservable pairs (fun _ => 1)) := by
    rw [plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover]
    exact div_pos (slotTotal_pos pairs _ (weight_positive A j) ∅ PairedLabels.fresh) hZ
  have hplain := accurate_plain pairs w (weight A j) (ratio A j) eta l hacc
  have hp0h := AnnealingMultipliers.empirical_positive hp0 he hplain.1
  have hpt (p r : (Labels A×Bool)×(Labels A×Bool)) (hp : p∈pairs) (hr : r∈pairs)
      (hpr : p≠r) : 0< chainMean pairs w (weight A j) (defectIndicator pairs p r) := by
    rw [defectIndicator_mean pairs PairedLabels.fresh PairedLabels.cover _ _ p r hp hr hpr]
    exact div_pos (mul_pos (hw p r)
      (slotDefect_pos pairs _ (weight_positive A j) ∅ PairedLabels.fresh p r hp hr hpr)) hZ
  have hpth (p r : (Labels A×Bool)×(Labels A×Bool)) (hp : p∈pairs) (hr : r∈pairs)
      (hpr : p≠r) : 0< empirical (defectIndicator pairs p r) l :=
    AnnealingMultipliers.empirical_positive (hpt p r hp hr hpr) he
      (accurate_defect pairs w (weight A j) (ratio A j) eta l hacc p r hp hr hpr).1
  have hb (p r : (Labels A×Bool)×(Labels A×Bool)) (hp : p∈pairs) (hr : r∈pairs)
      (hpr : p≠r) :
      (slotTotal pairs (weight A (j+1)) ∅/slotDefect pairs (weight A (j+1)) ∅ p r)/4≤
          learnedMultipliers pairs w l p r ∧
        learnedMultipliers pairs w l p r≤
          4*(slotTotal pairs (weight A (j+1)) ∅/slotDefect pairs (weight A (j+1)) ∅ p r) := by
    rw [learnedMultipliers,ite_eq_left ⟨hp,hr,hpr⟩]
    have hu := AnnealingMultipliers.update_good hp0 (hpt p r hp hr hpr) (hw p r)
      he0 he hplain (accurate_defect pairs w (weight A j) (ratio A j) eta l hacc p r hp hr hpr)
      (by simpa only [mul_div_assoc] using (weight_mean_identity pairs PairedLabels.fresh
        PairedLabels.cover (weight A j) (weight_positive A j) w hw p r hp hr hpr))
      (ideal_adjacent A j p r hp hr hpr)
    simpa only [mul_div_assoc] using hu
  refine ⟨?_,?_,?_⟩
  · intro p r
    unfold learnedMultipliers
    split_ifs with ht
    · exact mul_pos (hw p r) (div_pos hp0h (hpth p r ht.1 ht.2.1 ht.2.2))
    · exact hw p r
  · intro p hp r hr hpr
    simpa only [div_div,mul_comm] using (hb p r hp hr hpr).1
  · intro p hp r hr hpr
    simpa only [mul_div_assoc] using (hb p r hp hr hpr).2

/-- Relative accuracy of the actual counting and plain observations
bounds one logarithmic counting-ratio error by 4 eta. -/
theorem successful_phase_ratio_log (A : Instance I J) (j : ℕ)
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0< w p r) (eta : ℝ) (he0 : 0≤ eta) (he : eta≤1/4)
    (l : List (Set (Labels A×Bool)))
    (hacc : AccuratePhase pairs w (weight A j) (ratio A j) eta l) :
    |Real.log (empiricalRatio pairs (ratio A j) l/
      (slotTotal pairs (weight A (j+1)) ∅/slotTotal pairs (weight A j) ∅))|≤4*eta := by
  have hZ := chainTotal_pos pairs PairedLabels.fresh PairedLabels.cover w
    (weight A j) (weight_positive A j) hw
  have hC := slotTotal_pos pairs _ (weight_positive A j) ∅ PairedLabels.fresh
  have hC' := slotTotal_pos pairs _ (weight_positive A (j+1)) ∅ PairedLabels.fresh
  have hp : 0< chainMean pairs w (weight A j) (plainObservable pairs (ratio A j)) := by
    rw [ratio_mean]
    exact div_pos hC' hZ
  have hq : 0< chainMean pairs w (weight A j) (plainObservable pairs (fun _ => 1)) := by
    rw [plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover]
    exact div_pos hC hZ
  have hph := relative_error_bounds _ _ _ (hacc (.inr ()))
  simp only [phaseObservable] at hph
  have hqh := accurate_plain pairs w (weight A j) (ratio A j) eta l hacc
  have h := (AnnealingMultipliers.relative_ratio hp hq he0 he hph hqh).2.2.2
  rw [ratio_mean,plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover] at h
  unfold empiricalRatio
  convert h using 2
  congr 1
  field_simp [hZ.ne',hC.ne',hC'.ne']

end ContingencyTables.CompanionMultiplierUpdate

end OAI
