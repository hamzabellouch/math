import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionKernel

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.SelectedDeletion.ExperimentAudit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Kernel F} {c C : ℝ}

def outcomeWeight (κ : Kernel F) (M : MergedPairs F) : Option (Output F) → ℝ
  | none => 1 - fixedSuccessMass κ M
  | some s => κ M s

theorem outcomeWeight_nonneg (hκ : IsExperiment κ c C)
    (M : MergedPairs F) (o : Option (Output F)) : 0 ≤ outcomeWeight κ M o := by
  cases o with
  | none => exact sub_nonneg.mpr (hκ.2.1 M)
  | some s => exact hκ.1 M s

omit [Field F] in
theorem sum_outcomeWeight (M : MergedPairs F) :
    ∑ o, outcomeWeight κ M o = 1 := by
  rw [Fintype.sum_option]
  simp only [outcomeWeight, fixedSuccessMass]
  ring

def fixedOutcomeLaw (hκ : IsExperiment κ c C) (M : MergedPairs F) :
    PMF (Option (Output F)) :=
  PMF.ofFintype (fun o => ENNReal.ofReal (outcomeWeight κ M o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => outcomeWeight_nonneg hκ M o)]
    rw [sum_outcomeWeight]
    simp)

@[simp] theorem fixedOutcomeLaw_real (hκ : IsExperiment κ c C)
    (M : MergedPairs F) (o : Option (Output F)) :
    (fixedOutcomeLaw hκ M o).toReal = outcomeWeight κ M o :=
  ENNReal.toReal_ofReal (outcomeWeight_nonneg hκ M o)

def experimentLaw (hκ : IsExperiment κ c C) :
    PMF (MergedPairs F × Option (Output F)) :=
  (offsetLaw F).bind fun M => (fixedOutcomeLaw hκ M).map (fun o => (M, o))

theorem offset_marginal (hκ : IsExperiment κ c C) :
    (experimentLaw hκ).map Prod.fst = offsetLaw F := by
  rw [experimentLaw, PMF.map_bind]
  simp only [PMF.map_comp]
  change (offsetLaw F).bind (fun M =>
    (fixedOutcomeLaw hκ M).map (Function.const _ M)) = offsetLaw F
  simp

@[simp] theorem experimentLaw_apply (hκ : IsExperiment κ c C)
    (M : MergedPairs F) (o : Option (Output F)) :
    experimentLaw hκ (M, o) = (offsetLaw F) M * fixedOutcomeLaw hκ M o := by
  classical
  simp [experimentLaw, PMF.bind_apply, PMF.map_apply, tsum_fintype,
    Prod.mk.injEq, ite_and]

@[simp] theorem experimentLaw_real (hκ : IsExperiment κ c C)
    (M : MergedPairs F) (o : Option (Output F)) :
    (experimentLaw hκ (M, o)).toReal =
      ((offsetLaw F) M).toReal * outcomeWeight κ M o := by
  rw [experimentLaw_apply, ENNReal.toReal_mul, fixedOutcomeLaw_real]

def returnedEvent (E : MergedPairs F → Output F → Prop) :
    Set (MergedPairs F × Option (Output F)) :=
  {x | x.2.elim False (E x.1)}

theorem returnedEvent_probability (hκ : IsExperiment κ c C)
    (E : MergedPairs F → Output F → Prop) :
    ((experimentLaw hκ).toOuterMeasure (returnedEvent E)).toReal = jointMass κ E := by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_fintype, ENNReal.toReal_sum]
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_option]
    simp [returnedEvent, Set.indicator, ENNReal.toReal_mul, outcomeWeight,
      jointMass, Finset.mul_sum, apply_ite]
  · intro x _
    by_cases hx : x ∈ returnedEvent E
    · simp [Set.indicator, hx, PMF.apply_ne_top]
    · simp [Set.indicator, hx]

theorem success_probability (hκ : IsExperiment κ c C) :
    ((experimentLaw hκ).toOuterMeasure (returnedEvent (fun _ _ => True))).toReal =
      successMass κ := returnedEvent_probability hκ _

theorem fixedOutcomeLaw_of_bad_initial (hκ : IsExperiment κ c C)
    (M : MergedPairs F) (hM : ¬ InitialGood M c C) :
    fixedOutcomeLaw hκ M = PMF.pure none := by
  classical
  ext o
  cases o with
  | none => simp [fixedOutcomeLaw, outcomeWeight, fixedSuccessMass, hκ.2.2.1 M hM]
  | some s => simp [fixedOutcomeLaw, outcomeWeight, hκ.2.2.1 M hM]

theorem offset_event_probability (hκ : IsExperiment κ c C)
    (E : Set (MergedPairs F)) :
    ((experimentLaw hκ).toOuterMeasure (Prod.fst ⁻¹' E)).toReal =
      offsetEventProbability E := by
  rw [← PMF.toOuterMeasure_map_apply, offset_marginal]
  rfl

theorem successful_atom_supported (hκ : IsExperiment κ c C)
    (M : MergedPairs F) (s : Output F)
    (hpos : 0 < experimentLaw hκ (M, some s)) :
    (configuration M s).Valid ∧ (configuration M s).Compatible := by
  apply hκ.2.2.2 M s
  rw [experimentLaw_apply] at hpos
  have hw : 0 < fixedOutcomeLaw hκ M (some s) := by
    by_contra hn
    have hz : fixedOutcomeLaw hκ M (some s) = 0 := le_antisymm (le_of_not_gt hn) bot_le
    simp [hz] at hpos
  exact ENNReal.ofReal_pos.mp hw

theorem deletion_atom_probability (hκ : IsExperiment κ c C)
    (D : DeletionSet F 3) :
    ((experimentLaw hκ).toOuterMeasure
      (returnedEvent (fun M s => (configuration M s).deletedLines = D.val))).toReal =
      deletionJointMass κ D := returnedEvent_probability hκ _

end Balanced.SelectedDeletion.ExperimentAudit

end

end OAI
