import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletion
import OAI.Combinatorics.BalancedRyser.Incidence.CorePencil

namespace OAI

namespace Balanced.SelectedJointAssembly

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem offset_real_mass :
    ∑ M : MergedPairs F, ((offsetLaw F) M).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun M _ => (offsetLaw F).apply_ne_top M)]
  have h : ∑ M : MergedPairs F, (offsetLaw F) M = 1 := by
    simpa only [tsum_fintype] using (offsetLaw F).tsum_coe
  rw [h, ENNReal.toReal_one]

theorem jointMass_nonnegative (κ : SelectedDeletion.Kernel F)
    (hnonneg : ∀ M s, 0 ≤ κ M s) (E : MergedPairs F → SelectedDeletion.Output F → Prop) :
    0 ≤ SelectedDeletion.jointMass κ E := by
  unfold SelectedDeletion.jointMass
  apply Finset.sum_nonneg
  intro M _
  apply mul_nonneg ENNReal.toReal_nonneg
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact hnonneg M s
  · exact le_rfl

theorem successMass_le_one (κ : SelectedDeletion.Kernel F)
    (hsub : ∀ M, ∑ s, κ M s ≤ 1) : SelectedDeletion.successMass κ ≤ 1 := by
  unfold SelectedDeletion.successMass SelectedDeletion.jointMass
  simp only [ite_true]
  calc
    (∑ M, ((offsetLaw F) M).toReal * ∑ s, κ M s) ≤
        ∑ M, ((offsetLaw F) M).toReal * 1 :=
      Finset.sum_le_sum (fun M _ => mul_le_mul_of_nonneg_left (hsub M) ENNReal.toReal_nonneg)
    _ = 1 := by simp only [mul_one, offset_real_mass]

theorem successMass_le_three_errors (κ : SelectedDeletion.Kernel F)
    (hnonneg : ∀ M s, 0 ≤ κ M s)
    (E₁ E₂ E₃ : MergedPairs F → SelectedDeletion.Output F → Prop)
    (hcover : ∀ M s, 0 < κ M s → E₁ M s ∨ E₂ M s ∨ E₃ M s) :
    SelectedDeletion.successMass κ ≤ SelectedDeletion.jointMass κ E₁ +
      SelectedDeletion.jointMass κ E₂ + SelectedDeletion.jointMass κ E₃ := by
  have hpoint (M : MergedPairs F) (s : SelectedDeletion.Output F) :
      κ M s ≤ (if E₁ M s then κ M s else 0) +
        (if E₂ M s then κ M s else 0) + (if E₃ M s then κ M s else 0) := by
    by_cases hpos : 0 < κ M s
    · rcases hcover M s hpos with h₁ | h₂ | h₃
      all_goals split_ifs <;> linarith [hnonneg M s]
    · have hz : κ M s = 0 := le_antisymm (le_of_not_gt hpos) (hnonneg M s)
      simp only [hz, ite_self, add_zero, le_refl]
  unfold SelectedDeletion.successMass SelectedDeletion.jointMass
  simp only [ite_true]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro M _
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => hpoint M s))
    ENNReal.toReal_nonneg

theorem exists_positive_output_avoiding_three (κ : SelectedDeletion.Kernel F)
    (hnonneg : ∀ M s, 0 ≤ κ M s)
    (E₁ E₂ E₃ : MergedPairs F → SelectedDeletion.Output F → Prop)
    (hsmall : SelectedDeletion.jointMass κ E₁ + SelectedDeletion.jointMass κ E₂ +
      SelectedDeletion.jointMass κ E₃ < SelectedDeletion.successMass κ) :
    ∃ M s, 0 < κ M s ∧ ¬ E₁ M s ∧ ¬ E₂ M s ∧ ¬ E₃ M s := by
  by_contra hn
  have hcover : ∀ M s, 0 < κ M s → E₁ M s ∨ E₂ M s ∨ E₃ M s := by
    intro M s hpos
    by_cases h₁ : E₁ M s
    · exact Or.inl h₁
    by_cases h₂ : E₂ M s
    · exact Or.inr (Or.inl h₂)
    by_cases h₃ : E₃ M s
    · exact Or.inr (Or.inr h₃)
    exact False.elim (hn ⟨M, s, hpos, h₁, h₂, h₃⟩)
  exact (not_le_of_gt hsmall) (successMass_le_three_errors κ hnonneg E₁ E₂ E₃ hcover)

theorem coreConcentration_iff_pencilEvent (C : Configuration F) (ρ : ℝ) :
    C.CoreConcentration ρ ↔ CorePencilEvent (ρ / 4) C.deletedLines := by
  have hcore : uncoveredPoints C.deletedLines = C.core := by
    ext p
    simp only [uncoveredPoints, Configuration.core, Finset.mem_filter]
  unfold Configuration.CoreConcentration CorePencilEvent
  rw [hcore]
  constructor
  · intro h L hdisj hcard hcover
    exact h L (fun l hl hdel => Finset.disjoint_left.mp hdisj hl hdel) hcard hcover
  · intro h L hav hcard hcover
    exact h L (Finset.disjoint_left.mpr hav) hcard hcover

theorem exists_configuration_of_joint_errors
    (κ : SelectedDeletion.Kernel F) {c Cbound ρ : ℝ}
    (hexp : SelectedDeletion.IsExperiment κ c Cbound)
    (hsmall : SelectedDeletion.occupancyFailureMass κ ρ +
      SelectedDeletion.jointMass κ (fun M s =>
        ¬ (SelectedDeletion.configuration M s).CoreConcentration ρ) +
      SelectedDeletion.jointMass κ (fun M s =>
        ¬ (SelectedDeletion.configuration M s).LocalCondition) <
      SelectedDeletion.successMass κ) :
    ∃ C : Configuration F, C.Valid ∧ C.Compatible ∧
      C.Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ ∧
      C.CoreConcentration ρ ∧ C.LocalCondition := by
  obtain ⟨M, s, hpos, hO, hCore, hLocal⟩ := exists_positive_output_avoiding_three
    κ hexp.1 _ _ _ hsmall
  have hv := hexp.2.2.2 M s hpos
  exact ⟨SelectedDeletion.configuration M s, hv.1, hv.2,
    not_not.mp hO, not_not.mp hCore, not_not.mp hLocal⟩

end
end Balanced.SelectedJointAssembly

end OAI
