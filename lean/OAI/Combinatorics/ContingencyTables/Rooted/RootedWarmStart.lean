import OAI.Combinatorics.ContingencyTables.Rooted.RootedAnnealing
import OAI.Combinatorics.ContingencyTables.Counting.CompanionMinMass
import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitialDraw

namespace OAI

/-! # Actual companion transversal masses and adjacent warm starts -/

namespace ContingencyTables.RootedWarmStart

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing
open CompanionInitialization (freeTotal)
open TwoLiftStates LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The initial factorial weight is independent of the selected root. -/
lemma zero_weight_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    weight A R 0=CompanionAnnealing.weight A 0 := by
  funext S
  unfold weight CompanionAnnealing.weight
  simp only [Nat.cast_zero,zero_div]
  unfold RootedFactorialApplication.f CompanionFactorialApplication.f firstLift
  rw [RootedCountIdentification.h_zero,CompanionInitialization.h_zero]
  rfl

lemma total_zero (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    slotTotal pairs (weight A R 0) ∅=
      freeTotal A*∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1) := by
  rw [zero_weight_eq]
  simpa only [CompanionAnnealing.weight,Nat.cast_zero,zero_div] using
    CompanionInitialization.total_zero A

noncomputable def total (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) : ℝ := slotTotal pairs (weight A R j) ∅

lemma total_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) : 0< total A R j :=
  slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh

noncomputable def law (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) : ℝ :=
  weight A R j S/total A R j

private lemma free_positive (A : Instance I J) : 0< freeTotal A := by
  apply Finset.prod_pos
  intro a _
  exact Nat.cast_pos.mpr (Nat.succ_pos _)

/-- The exact phase-j transversal law is two-warm for phase j+1.
The statement applies in particular to every actual paired transversal. -/
theorem law_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    law A R j S≤2*law A R (j+1) S := by
  have hS := weight_adjacent A R j S
  have hT := total_adjacent A R j pairs ∅
  have h0 := total_positive A R j
  have h1 := total_positive A R (j+1)
  have hweight := weight_positive A R j S
  unfold law
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ h0 h1).mpr
  unfold total at *
  nlinarith [mul_le_mul_of_nonneg_left hT.2 hweight.le,
    mul_le_mul_of_nonneg_right hS.1 h0.le]

theorem weight_bounds_zero (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2:ℝ)^j*weight A R 0 S≤ weight A R j S ∧ weight A R j S≤ weight A R 0 S := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := weight_adjacent A R j S
    constructor
    · rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left ih.1 (show (0:ℝ)≤1/2 by norm_num)]
    · exact h.2.trans ih.2

theorem total_bounds_zero (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) :
    (1/2:ℝ)^j*total A R 0≤ total A R j ∧ total A R j≤ total A R 0 := by
  unfold total
  constructor
  · rw [← slotTotal_scale]
    exact slotTotal_mono _ _ _ (fun S => (weight_bounds_zero A R j S).1) _
  · exact slotTotal_mono _ _ _ (fun S => (weight_bounds_zero A R j S).2) _

lemma zero_weight_lower (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (S : Set (Labels A×Bool)) :
    freeTotal A/CompanionFactorialApplication.denominator A≤ weight A R 0 S := by
  rw [zero_weight_eq]
  exact CompanionWarmStart.zero_weight_lower A S

/-- An explicit positive minimum mass for the actual transversal law.
Its binary size depends on j and the bounded small-cell capacities. -/
theorem law_lower (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2:ℝ)^j/(CompanionFactorialApplication.denominator A*
      ∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤ law A R j S := by
  have hM := free_positive A
  have hD := CompanionFactorialApplication.denominator_positive A
  have hB : 0<(∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) :=
    Finset.prod_pos (fun _ _ => by positivity)
  have hweight := weight_bounds_zero A R j S
  have hz := zero_weight_lower A R S
  have hT := (total_bounds_zero A R j).2
  have hT0 : total A R 0=freeTotal A*∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1) := by
    unfold total weight
    exact total_zero A R
  rw [hT0] at hT
  have hpositive := total_positive A R j
  have hpow : 0≤(1/2:ℝ)^j := by positivity
  unfold law
  rw [div_le_div_iff₀ (mul_pos hD hB) hpositive]
  have hlo : (1/2:ℝ)^j*freeTotal A≤ weight A R j S*CompanionFactorialApplication.denominator A := by
    have hz' := (div_le_iff₀ hD).mp hz
    have hmul := mul_le_mul_of_nonneg_right hweight.1 hD.le
    have hmul' := mul_le_mul_of_nonneg_left hz' hpow
    nlinarith
  have hupper := mul_le_mul_of_nonneg_left hT hpow
  have hfinal := mul_le_mul_of_nonneg_right hlo hB.le
  nlinarith

/-- The existing executed initializer is exactly the selected-root phase-zero law. -/
lemma law_zero_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (S : Set (Labels A×Bool)) :
    law A R 0 S=CompanionWarmStart.law A 0 S := by
  unfold law total CompanionWarmStart.law CompanionWarmStart.total
  rw [zero_weight_eq]

lemma ideal_initial_mass (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (S : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
    ((CompanionInitialDraw.idealLaw A).mass S:ℝ)=law A R 0 S.val.val := by
  rw [law_zero_eq]
  exact CompanionInitialDraw.idealLaw_mass A S

theorem initial_distance (A : Instance I J) (R : RootedCompletion.Selection A.T) (h : ℕ) :
    RealKernelApproximation.distance
      (fun S => ((FirstSuccess.mapLaw
        (FirstSuccess.uniformLaw (α := Fin (CompanionInitialDraw.initialBits A
          (CompanionInitialDraw.precision A h)) → Bool))
        (CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h))).mass S:ℝ))
      (fun S => law A R 0 S.val.val)≤1/(2:ℝ)^h := by
  simp_rw [law_zero_eq]
  exact CompanionInitialDraw.initial_distance A h

lemma actual_degree (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) :
    BinaryContraction.DegreePositive (weight A R j)
      (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length ∧
    BinaryContraction.OmissionProperty (weight A R j)
      (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length := by
  have hs := RootedFactorialApplication.first_properties A R ((j:ℝ)/CompanionAnnealing.scale A)
    (div_nonneg (Nat.cast_nonneg j) (CompanionAnnealing.scale_positive A).le)
  simpa only [weight,PairedLabels.length] using hs

lemma initial_weight_lower (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (S : Set (Labels A×Bool)) (hS : PlainState pairs S) :
    freeTotal A*(1/2:ℝ)^Fintype.card (Labels A)≤ weight A R 0 S := by
  rw [zero_weight_eq]
  exact CompanionMinMass.initial_weight_lower A S hS

/-- The sharp source minimum mass uses only the original bounded-cell label count. -/
theorem plain_law_lower (A : Instance I J) (R : RootedCompletion.Selection A.T) (K j : ℕ)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤(2:ℝ)^K)
    (S : Set (Labels A×Bool)) (hS : PlainState pairs S) :
    (1/2:ℝ)^(j+Fintype.card (Labels A)+K)≤ law A R j S := by
  have hM := free_positive A
  have hT := (total_bounds_zero A R j).2
  have hT0 : total A R 0=freeTotal A*∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1) :=
    total_zero A R
  rw [hT0] at hT
  have hupper : total A R j≤ freeTotal A*(2:ℝ)^K :=
    hT.trans (mul_le_mul_of_nonneg_left hB hM.le)
  have hw := (weight_bounds_zero A R j S).1
  have hi := initial_weight_lower A R S hS
  have hlower : freeTotal A*(1/2:ℝ)^(j+Fintype.card (Labels A))≤ weight A R j S := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hi (show (0:ℝ)≤(1/2:ℝ)^j by positivity)]
  have hpos := total_positive A R j
  unfold law
  rw [le_div_iff₀ hpos,pow_add]
  have hm := mul_le_mul_of_nonneg_left hupper
    (show (0:ℝ)≤(1/2:ℝ)^(j+Fintype.card (Labels A))*(1/2:ℝ)^K by positivity)
  have hcancel : (1/2:ℝ)^K*(2:ℝ)^K=1 := by
    rw [←mul_pow]
    norm_num
  have he : ((1/2:ℝ)^(j+Fintype.card (Labels A))*(1/2:ℝ)^K)*
      (freeTotal A*(2:ℝ)^K)=freeTotal A*(1/2:ℝ)^(j+Fintype.card (Labels A)) := by
    calc
      _=freeTotal A*(1/2:ℝ)^(j+Fintype.card (Labels A))*
          ((1/2:ℝ)^K*(2:ℝ)^K) := by ring
      _=_ := by rw [hcancel,mul_one]
  rw [he] at hm
  exact hm.trans hlower

end ContingencyTables.RootedWarmStart

end OAI
