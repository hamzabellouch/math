import OAI.Combinatorics.BalancedRyser.Local.LocalConfigurationPattern

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def LargePencilEvent (C : Configuration F) : Prop :=
  ∃ p, logBudget F < C.splitMultiplicity p

def HighReuseEvent (C : Configuration F) : Prop :=
  ∃ p, 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p

def SmallBadPatternEvent (C : Configuration F) : Prop :=
  ∃ p, 3 ≤ C.splitMultiplicity p ∧ C.splitMultiplicity p ≤ logBudget F ∧
    reuseCount C p ≤ 2 ∧
    ∃ (P : EqualityPattern (C.splitMultiplicity p) (reuseCount C p))
      (a : DirectionAssignment F (C.splitMultiplicity p) (reuseCount C p))
      (side : Bits (C.splitMultiplicity p)),
      Eligible P a ∧ AdmissibleBadCover P a side p C.merged ∧
      ∃ used : Fin (C.splitMultiplicity p) → Slot F, Function.Injective used ∧
        ∀ i, (used i).1 = a.1 i ∧
          (C.choice (used i)).tuple = prescribedTuple P a side i ∧
          (C.choice (used i)).line = lineThrough (a.1 i) p

theorem positive_kernel_local_failure_cases
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hK : KernelConditions Q w K) (M : MergedPairs F) (v : Output F)
    (hw : 0 < w M v) (hbad : ¬ (configuration M v).LocalCondition) :
    LargePencilEvent (configuration M v) ∨ HighReuseEvent (configuration M v) ∨
      SmallBadPatternEvent (configuration M v) := by
  obtain ⟨hV, hC, _, hcap⟩ := hK.2.2.1 M v hw
  unfold Configuration.LocalCondition at hbad
  push Not at hbad
  obtain ⟨p, hb, hA⟩ := hbad
  by_cases hlarge : logBudget F < (configuration M v).splitMultiplicity p
  · exact Or.inl ⟨p, hlarge⟩
  by_cases hre : 3 ≤ reuseCount (configuration M v) p
  · exact Or.inr (Or.inl ⟨p, by omega, hre⟩)
  let C := configuration M v
  refine Or.inr (Or.inr ⟨p, hb, by omega, by omega,
    ConfigurationPattern.pattern C hV hC p, ConfigurationPattern.assignment C hV hC p,
    ConfigurationPattern.bits C hV hC p,
    ConfigurationPattern.assignment_eligible C hV hC p,
    ⟨ConfigurationPattern.admissible C hV hC p (by change 2 ≤ (configuration M v).splitMultiplicity p; omega) hcap,
      (ConfigurationPattern.badCover_iff C hV hC p).mpr hA⟩,
    ConfigurationPattern.slot C hV hC p, ConfigurationPattern.slot_injective C hV hC p, ?_⟩)
  intro i
  exact ⟨rfl, (ConfigurationPattern.prescribedTuple_eq C hV hC p i).symm,
    ConfigurationPattern.slot_line_eq C hV hC p i⟩

omit [Field F] in

theorem selectedProbability_le_three_of_positive_imp
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (E A B D : Configuration F → Prop)
    (himp : ∀ M v, 0 < w M v → E (configuration M v) →
      A (configuration M v) ∨ B (configuration M v) ∨ D (configuration M v)) :
    selectedProbability w E ≤ selectedProbability w A +
      selectedProbability w B + selectedProbability w D := by
  unfold selectedProbability
  rw [← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro M _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  by_cases hp : 0 < w M v
  · have hnonneg := hw M v
    by_cases he : E (configuration M v)
    · rcases himp M v hp he with ha | hb | hd
      · simp only [ite_eq_left he, ite_eq_left ha]
        split_ifs <;> linarith
      · simp only [ite_eq_left he, ite_eq_left hb]
        split_ifs <;> linarith
      · simp only [ite_eq_left he, ite_eq_left hd]
        split_ifs <;> linarith
    · simp only [ite_eq_right he]
      positivity
  · have hz : w M v = 0 := le_antisymm (le_of_not_gt hp) (hw M v)
    simp only [hz, ite_self, add_zero, le_refl]

theorem local_failure_probability_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hK : KernelConditions Q w K) :
    selectedProbability w (fun C => ¬ C.LocalCondition) ≤
      selectedProbability w LargePencilEvent + selectedProbability w HighReuseEvent +
        selectedProbability w SmallBadPatternEvent := by
  apply selectedProbability_le_three_of_positive_imp w hK.1
  intro M v hw hbad
  exact positive_kernel_local_failure_cases Q w K hK M v hw hbad

end
end Balanced.Local

end OAI
