import OAI.Combinatorics.BalancedRyser.Deletion.ConfigurationDeletion
import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionBound

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.SelectedDeletion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Kernel F} {c C : ℝ}

theorem jointMass_nonneg (hnonneg : ∀ M s, 0 ≤ κ M s)
    (E : MergedPairs F → Output F → Prop) : 0 ≤ jointMass κ E := by
  classical
  apply Finset.sum_nonneg
  intro M _
  apply mul_nonneg ENNReal.toReal_nonneg
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact hnonneg M s
  · exact le_rfl

theorem successMass_nonneg (hnonneg : ∀ M s, 0 ≤ κ M s) :
    0 ≤ successMass κ := jointMass_nonneg hnonneg _

theorem deletionJointMass_nonneg (hnonneg : ∀ M s, 0 ≤ κ M s)
    (D : DeletionSet F 3) : 0 ≤ deletionJointMass κ D :=
  jointMass_nonneg hnonneg _

theorem sum_deletionIndicator (hκ : IsExperiment κ c C)
    (M : MergedPairs F) (s : Output F) :
    (∑ D : DeletionSet F 3,
      if (configuration M s).deletedLines = D.val then κ M s else 0) = κ M s := by
  classical
  by_cases hz : κ M s = 0
  · simp [hz]
  have hpos : 0 < κ M s := lt_of_le_of_ne (hκ.1 M s) (Ne.symm hz)
  have hvalid := hκ.2.2.2 M s hpos
  let D₀ : DeletionSet F 3 :=
    ⟨(configuration M s).deletedLines,
      (configuration M s).deletedLines_isDeletionSet hvalid.1 hvalid.2⟩
  have heq : ∀ D : DeletionSet F 3,
      (configuration M s).deletedLines = D.val ↔ D = D₀ := by
    intro D
    constructor
    · intro h
      exact Subtype.ext h.symm
    · intro h
      subst D
      rfl
  simp_rw [heq]
  simp

theorem sum_deletionJointMass (hκ : IsExperiment κ c C) :
    ∑ D : DeletionSet F 3, deletionJointMass κ D = successMass κ := by
  classical
  simp only [deletionJointMass, jointMass, successMass, ite_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  convert sum_deletionIndicator hκ M s using 1
  apply Finset.sum_congr rfl
  intro D _
  by_cases h : (configuration M s).deletedLines = D.val <;> simp [h]

theorem sum_normalizedDeletionJointMass (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ) :
    (∑ D : DeletionSet F 3, deletionJointMass κ D / successMass κ) = 1 := by
  rw [← Finset.sum_div, sum_deletionJointMass hκ]
  exact div_self (ne_of_gt hsuccess)

def conditionalDeletionLaw (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ) : PMF (DeletionSet F 3) :=
  PMF.ofFintype (fun D => ENNReal.ofReal (deletionJointMass κ D / successMass κ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun D _ => div_nonneg (deletionJointMass_nonneg hκ.1 D) hsuccess.le)]
    rw [sum_normalizedDeletionJointMass hκ hsuccess]
    simp)

@[simp] theorem conditionalDeletionLaw_apply_toReal (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ) (D : DeletionSet F 3) :
    (conditionalDeletionLaw hκ hsuccess D).toReal =
      deletionJointMass κ D / successMass κ := by
  exact ENNReal.toReal_ofReal
    (div_nonneg (deletionJointMass_nonneg hκ.1 D) hsuccess.le)

theorem conditionalDeletionLaw_realizes (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ) :
    RealizesConditionalLaw κ (conditionalDeletionLaw hκ hsuccess) :=
  conditionalDeletionLaw_apply_toReal hκ hsuccess

theorem exists_realizing_dominated_law (hκ : IsExperiment κ c C)
    {K a₀ : ℝ} (hq : 3 ≤ Fintype.card F) (hK : 0 ≤ K) (ha₀ : 0 < a₀)
    (hcyl : ∀ M (J : Finset (Slot F)) (f : Output F),
      fixedCylinderMass κ M J f ≤ (K / Fintype.card F) ^ J.card)
    (hsuccess : a₀ ≤ successMass κ) :
    ∃ Q : PMF (DeletionSet F 3),
      RealizesConditionalLaw κ Q ∧ DeletionDominated 3 (a₀⁻¹ + 4 * K) Q := by
  let Q := conditionalDeletionLaw hκ (ha₀.trans_le hsuccess)
  have hQ : RealizesConditionalLaw κ Q := conditionalDeletionLaw_realizes hκ _
  exact ⟨Q, hQ, realizesConditionalLaw_dominated hq hK ha₀ hκ.1 hcyl hsuccess Q hQ⟩

end Balanced.SelectedDeletion

end

end OAI
