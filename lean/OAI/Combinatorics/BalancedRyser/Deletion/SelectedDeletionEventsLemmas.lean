import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionPMF

namespace OAI

section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Balanced.SelectedDeletion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Kernel F} {c C : ℝ}

theorem sum_deletionEventIndicator (hκ : IsExperiment κ c C)
    (E : Finset (Line F) → Prop) (M : MergedPairs F) (s : Output F) :
    (∑ D : DeletionSet F 3,
      if E D.val then
        (if (configuration M s).deletedLines = D.val then κ M s else 0)
      else 0) =
      if E (configuration M s).deletedLines then κ M s else 0 := by
  classical
  calc
    _ = ∑ D : DeletionSet F 3,
        if (configuration M s).deletedLines = D.val then
          (if E (configuration M s).deletedLines then κ M s else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro D _
      by_cases h : (configuration M s).deletedLines = D.val
      · simp [h]
      · simp [h]
    _ = _ := by
      by_cases hE : E (configuration M s).deletedLines
      · simp only [ite_eq_left hE]
        exact sum_deletionIndicator hκ M s
      · simp [hE]

theorem sum_event_deletionJointMass (hκ : IsExperiment κ c C)
    (E : Finset (Line F) → Prop) :
    (∑ D : DeletionSet F 3, if E D.val then deletionJointMass κ D else 0) =
      jointMass κ (fun M s => E (configuration M s).deletedLines) := by
  classical
  have hsplit : ∀ D : DeletionSet F 3,
      (if E D.val then deletionJointMass κ D else 0) =
      ∑ M, ((offsetLaw F) M).toReal * ∑ s,
        if E D.val then
          (if (configuration M s).deletedLines = D.val then κ M s else 0)
        else 0 := by
    intro D
    by_cases h : E D.val
    · simp only [ite_eq_left h, deletionJointMass, jointMass]
      apply Finset.sum_congr rfl
      intro M _
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
    · simp [h]
  simp_rw [hsplit]
  unfold jointMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  convert sum_deletionEventIndicator hκ E M s using 1

theorem realizingLaw_eventProbability (hκ : IsExperiment κ c C)
    (Q : PMF (DeletionSet F 3)) (hQ : RealizesConditionalLaw κ Q)
    (E : Finset (Line F) → Prop) :
    deletionEventProbability Q (fun D => E D.val) =
      jointMass κ (fun M s => E (configuration M s).deletedLines) / successMass κ := by
  classical
  change (∑ D : DeletionSet F 3, if E D.val then (Q D).toReal else 0) = _
  calc
    _ = ∑ D : DeletionSet F 3,
        (if E D.val then deletionJointMass κ D else 0) / successMass κ := by
      apply Finset.sum_congr rfl
      intro D _
      by_cases h : E D.val
      · simpa only [ite_eq_left h] using hQ D
      · simp [h]
    _ = _ := by rw [← Finset.sum_div, sum_event_deletionJointMass hκ E]

theorem jointMass_eq_success_mul_eventProbability (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ)
    (Q : PMF (DeletionSet F 3)) (hQ : RealizesConditionalLaw κ Q)
    (E : Finset (Line F) → Prop) :
    jointMass κ (fun M s => E (configuration M s).deletedLines) =
      successMass κ * deletionEventProbability Q (fun D => E D.val) := by
  rw [realizingLaw_eventProbability hκ Q hQ E]
  field_simp [ne_of_gt hsuccess]

end Balanced.SelectedDeletion

end

section

namespace Balanced.SelectedDeletion

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Kernel F} {c C : ℝ}

theorem realizingLaw_unique {Q R : PMF (DeletionSet F 3)}
    (hQ : RealizesConditionalLaw κ Q) (hR : RealizesConditionalLaw κ R) :
    Q = R := by
  ext D
  apply (ENNReal.toReal_eq_toReal_iff' (Q.apply_ne_top D) (R.apply_ne_top D)).mp
  exact (hQ D).trans (hR D).symm

theorem realizingLaw_successMass_ne_zero (Q : PMF (DeletionSet F 3))
    (hQ : RealizesConditionalLaw κ Q) : successMass κ ≠ 0 := by
  intro hz
  have hzero : ∀ D, Q D = 0 := by
    intro D
    apply (ENNReal.toReal_eq_toReal_iff' (Q.apply_ne_top D) ENNReal.zero_ne_top).mp
    simpa only [hz, div_zero, ENNReal.toReal_zero] using hQ D
  have htotal := Q.tsum_coe
  simp only [hzero, tsum_zero] at htotal
  exact zero_ne_one htotal

theorem realizingLaw_successMass_pos
    (hnonneg : ∀ M s, 0 ≤ κ M s) (Q : PMF (DeletionSet F 3))
    (hQ : RealizesConditionalLaw κ Q) : 0 < successMass κ :=
  lt_of_le_of_ne (successMass_nonneg hnonneg)
    (Ne.symm (realizingLaw_successMass_ne_zero Q hQ))

theorem realizingLaw_eq_conditionalDeletionLaw (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ) (Q : PMF (DeletionSet F 3))
    (hQ : RealizesConditionalLaw κ Q) :
    Q = conditionalDeletionLaw hκ hsuccess :=
  realizingLaw_unique hQ (conditionalDeletionLaw_realizes hκ hsuccess)

theorem existsUnique_realizingLaw_iff (hκ : IsExperiment κ c C) :
    (∃! Q : PMF (DeletionSet F 3), RealizesConditionalLaw κ Q) ↔
      0 < successMass κ := by
  constructor
  · rintro ⟨Q, hQ, _⟩
    exact realizingLaw_successMass_pos hκ.1 Q hQ
  · intro hs
    refine ⟨conditionalDeletionLaw hκ hs, conditionalDeletionLaw_realizes hκ hs, ?_⟩
    intro Q hQ
    exact realizingLaw_eq_conditionalDeletionLaw hκ hs Q hQ

theorem not_realizingLaw_of_successMass_zero (hz : successMass κ = 0)
    (Q : PMF (DeletionSet F 3)) : ¬ RealizesConditionalLaw κ Q := by
  intro hQ
  exact realizingLaw_successMass_ne_zero Q hQ hz

end Balanced.SelectedDeletion

end

section

namespace Balanced.SelectedDeletion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem uniformDeletionMass_three_pos (hq : 3 ≤ Fintype.card F) :
    0 < uniformDeletionMass (F := F) 3 := by
  rw [GeometricDeletionCounting.uniformDeletionMass_eq]
  have hc : (0 : ℝ) < Nat.choose (Fintype.card F) 3 := by
    exact_mod_cast Nat.choose_pos hq
  positivity

theorem realizesConditionalLaw_ratio_le {κ : Kernel F} {K a₀ : ℝ}
    (hq : 3 ≤ Fintype.card F) (hK : 0 ≤ K) (ha₀ : 0 < a₀)
    (hnonneg : ∀ M s, 0 ≤ κ M s)
    (hcyl : ∀ M (J : Finset (Slot F)) (f : Output F),
      fixedCylinderMass κ M J f ≤ (K / Fintype.card F) ^ J.card)
    (hsuccess : a₀ ≤ successMass κ)
    (Q : PMF (DeletionSet F 3)) (hQ : RealizesConditionalLaw κ Q)
    (D : DeletionSet F 3) :
    (Q D).toReal / uniformDeletionMass (F := F) 3 ≤
      a₀⁻¹ * (K ^ 2 * (1 - 1 / (Fintype.card F : ℝ)) *
        (1 - 2 / (Fintype.card F : ℝ))) ^ (Fintype.card F + 1) := by
  have hspos : 0 < successMass κ := ha₀.trans_le hsuccess
  have hupos := uniformDeletionMass_three_pos (F := F) hq
  let A : ℝ := (6 : ℝ) ^ (Fintype.card F + 1) *
    ((K / Fintype.card F) ^ (2 * (Fintype.card F + 1)) /
      (Fintype.card F : ℝ) ^ (Fintype.card F + 1))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hraw : deletionJointMass κ D ≤ A :=
    deletionJointMass_le_of_atom_bound κ hnonneg
      ((K / Fintype.card F) ^ (2 * (Fintype.card F + 1)))
      (by positivity) (atom_le_of_fixed_cylinders hcyl) D
  have hcond : deletionJointMass κ D / successMass κ ≤ A / a₀ :=
    (div_le_div_of_nonneg_right hraw hspos.le).trans
      (div_le_div_of_nonneg_left hA ha₀ hsuccess)
  rw [hQ D]
  calc
    _ ≤ (A / a₀) / uniformDeletionMass (F := F) 3 :=
      div_le_div_of_nonneg_right hcond hupos.le
    _ = a₀⁻¹ * (A /
        DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1)) := by
      rw [GeometricDeletionCounting.uniformDeletionMass_eq]
      unfold DeletionLaw.uniformDeletionMass
      ring
    _ = _ := by
      dsimp [A]
      rw [DeletionLaw.assignment_ratio_exact hq]

theorem conditionalDeletionLaw_ratio_le {κ : Kernel F} {c C K a₀ : ℝ}
    (hκ : IsExperiment κ c C)
    (hq : 3 ≤ Fintype.card F) (hK : 0 ≤ K) (ha₀ : 0 < a₀)
    (hcyl : ∀ M (J : Finset (Slot F)) (f : Output F),
      fixedCylinderMass κ M J f ≤ (K / Fintype.card F) ^ J.card)
    (hsuccess : a₀ ≤ successMass κ) (D : DeletionSet F 3) :
    (conditionalDeletionLaw hκ (ha₀.trans_le hsuccess) D).toReal /
        uniformDeletionMass (F := F) 3 ≤
      a₀⁻¹ * (K ^ 2 * (1 - 1 / (Fintype.card F : ℝ)) *
        (1 - 2 / (Fintype.card F : ℝ))) ^ (Fintype.card F + 1) :=
  realizesConditionalLaw_ratio_le hq hK ha₀ hκ.1 hcyl hsuccess
    (conditionalDeletionLaw hκ (ha₀.trans_le hsuccess))
    (conditionalDeletionLaw_realizes hκ (ha₀.trans_le hsuccess)) D

end Balanced.SelectedDeletion

end

end OAI
