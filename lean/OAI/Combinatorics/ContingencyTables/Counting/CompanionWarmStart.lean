import OAI.Combinatorics.ContingencyTables.Counting.CompanionAnnealing
import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitialization

namespace OAI

/-! # Actual companion transversal masses and adjacent warm starts -/

namespace ContingencyTables.CompanionWarmStart

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing CompanionInitialization
open TwoLiftStates LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def total (A : Instance I J) (j : ℕ) : ℝ := slotTotal pairs (weight A j) ∅

lemma total_positive (A : Instance I J) (j : ℕ) : 0< total A j :=
  slotTotal_pos pairs _ (weight_positive A j) ∅ PairedLabels.fresh

noncomputable def law (A : Instance I J) (j : ℕ) (S : Set (Labels A×Bool)) : ℝ :=
  weight A j S/total A j

private lemma free_positive (A : Instance I J) : 0< freeTotal A := by
  apply Finset.prod_pos
  intro a _
  exact Nat.cast_pos.mpr (Nat.succ_pos _)

/-- The exact phase-j transversal law is two-warm for phase j+1.
The statement applies in particular to every actual paired transversal. -/
theorem law_adjacent (A : Instance I J) (j : ℕ) (S : Set (Labels A×Bool)) :
    law A j S≤2*law A (j+1) S := by
  have hS := weight_adjacent A j S
  have hT := total_adjacent A j pairs ∅
  have h0 := total_positive A j
  have h1 := total_positive A (j+1)
  have hweight := weight_positive A j S
  unfold law
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ h0 h1).mpr
  unfold total at *
  nlinarith [mul_le_mul_of_nonneg_left hT.2 hweight.le,
    mul_le_mul_of_nonneg_right hS.1 h0.le]

theorem weight_bounds_zero (A : Instance I J) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2:ℝ)^j*weight A 0 S≤ weight A j S ∧ weight A j S≤ weight A 0 S := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := weight_adjacent A j S
    constructor
    · rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left ih.1 (show (0:ℝ)≤1/2 by norm_num)]
    · exact h.2.trans ih.2

theorem total_bounds_zero (A : Instance I J) (j : ℕ) :
    (1/2:ℝ)^j*total A 0≤ total A j ∧ total A j≤ total A 0 := by
  unfold total
  constructor
  · rw [← slotTotal_scale]
    exact slotTotal_mono _ _ _ (fun S => (weight_bounds_zero A j S).1) _
  · exact slotTotal_mono _ _ _ (fun S => (weight_bounds_zero A j S).2) _

lemma zero_weight_lower (A : Instance I J) (S : Set (Labels A×Bool)) :
    freeTotal A/CompanionFactorialApplication.denominator A≤ weight A 0 S := by
  unfold weight
  simp only [Nat.cast_zero,zero_div]
  unfold f firstLift
  rw [h_zero]
  have hf : (1:ℝ)≤ FactorialSignatures.factorialProduct
      (groupCount (group (labelCell A)) S) := by
    unfold FactorialSignatures.factorialProduct
    apply Finset.one_le_prod₀
    intro u _
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
  exact div_le_div_of_nonneg_right (by nlinarith [free_positive A])
    (CompanionFactorialApplication.denominator_positive A).le

/-- An explicit positive minimum mass for the actual transversal law.
Its binary size depends on j and the bounded small-cell capacities. -/
theorem law_lower (A : Instance I J) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2:ℝ)^j/(CompanionFactorialApplication.denominator A*
      ∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤ law A j S := by
  have hM := free_positive A
  have hD := CompanionFactorialApplication.denominator_positive A
  have hB : 0<(∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) :=
    Finset.prod_pos (fun _ _ => by positivity)
  have hweight := weight_bounds_zero A j S
  have hz := zero_weight_lower A S
  have hT := (total_bounds_zero A j).2
  have hT0 : total A 0=freeTotal A*∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1) := by
    unfold total weight
    simpa only [Nat.cast_zero,zero_div] using total_zero A
  rw [hT0] at hT
  have hpositive := total_positive A j
  have hpow : 0≤(1/2:ℝ)^j := by positivity
  unfold law
  rw [div_le_div_iff₀ (mul_pos hD hB) hpositive]
  have hlo : (1/2:ℝ)^j*freeTotal A≤ weight A j S*CompanionFactorialApplication.denominator A := by
    have hz' := (div_le_iff₀ hD).mp hz
    have hmul := mul_le_mul_of_nonneg_right hweight.1 hD.le
    have hmul' := mul_le_mul_of_nonneg_left hz' hpow
    nlinarith
  have hupper := mul_le_mul_of_nonneg_left hT hpow
  have hfinal := mul_le_mul_of_nonneg_right hlo hB.le
  nlinarith

end ContingencyTables.CompanionWarmStart

end OAI
