import OAI.NumberTheory.Ostmann.Construction.ScheduledPriorFubini

namespace OAI

/-! # The copied H priors and the single retained Y prior -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledCopiedAssignment {I A : Type*}
    (role : I → CopyScheduleRole) (n : ℕ)
    (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) :
    {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A :=
  fun i => match copyScheduleSurvivorEquiv role n i with
    | .inl (true, h) => l h
    | .inl (false, h) => r h
    | .inr y => u y

theorem scheduledCopiedAssignment_left {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) (h : CopyScheduleH role n) :
    scheduledCopiedAssignment role n u l r (scheduledOutputVertex role n (.inl (true, h))) = l h := by
  simp only [scheduledCopiedAssignment, scheduledOutputVertex, Equiv.apply_symm_apply]

theorem scheduledCopiedAssignment_right {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) (h : CopyScheduleH role n) :
    scheduledCopiedAssignment role n u l r (scheduledOutputVertex role n (.inl (false, h))) = r h := by
  simp only [scheduledCopiedAssignment, scheduledOutputVertex, Equiv.apply_symm_apply]

theorem scheduledCopiedAssignment_outside {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) (y : CopyScheduleY role n) :
    scheduledCopiedAssignment role n u l r (scheduledOutputVertex role n (.inr y)) = u y := by
  simp only [scheduledCopiedAssignment, scheduledOutputVertex, Equiv.apply_symm_apply]

noncomputable def scheduledCopiedAssignmentEquiv {I A : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) :
    ((CopyScheduleY role n → A) × ((CopyScheduleH role n → A) × (CopyScheduleH role n → A))) ≃
      ({i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A) where
  toFun a := scheduledCopiedAssignment role n a.1 a.2.1 a.2.2
  invFun a := ((fun y => a (scheduledOutputVertex role n (.inr y))),
    (fun h => a (scheduledOutputVertex role n (.inl (true, h)))),
    (fun h => a (scheduledOutputVertex role n (.inl (false, h)))))
  left_inv a := by
    apply Prod.ext
    · funext y
      exact scheduledCopiedAssignment_outside role n a.1 a.2.1 a.2.2 y
    · apply Prod.ext
      · funext h
        exact scheduledCopiedAssignment_left role n a.1 a.2.1 a.2.2 h
      · funext h
        exact scheduledCopiedAssignment_right role n a.1 a.2.1 a.2.2 h
  right_inv a := by
    funext j
    obtain ⟨i, rfl⟩ := (copyScheduleSurvivorEquiv role n).symm.surjective j
    dsimp only
    rcases i with ⟨b, h⟩ | y
    · cases b
      · exact scheduledCopiedAssignment_right role n _ _ _ h
      · exact scheduledCopiedAssignment_left role n _ _ _ h
    · exact scheduledCopiedAssignment_outside role n _ _ _ y

theorem scheduledCopiedAssignment_prior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ)
    (μ : {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A → ℝ)
    (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) :
    (∏ i, μ i (scheduledCopiedAssignment role n u l r i)) =
      (∏ y, μ (scheduledOutputVertex role n (.inr y)) (u y)) *
      (∏ h, μ (scheduledOutputVertex role n (.inl (true, h))) (l h)) *
      (∏ h, μ (scheduledOutputVertex role n (.inl (false, h))) (r h)) := by
  rw [← (copyScheduleSurvivorEquiv role n).symm.prod_comp]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool,
    scheduledOutputVertex, scheduledCopiedAssignment, Equiv.apply_symm_apply]
  ring

/-- The off-diagonal sum samples two independent H copies and retains one Y.
No second outside prior is inserted when passing to the next level. -/
theorem copied_prior_fubini {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n : ℕ)
    (μ : {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A → ℝ)
    (F : ({i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A) → ℂ) :
    (∑ a, ((∏ i, μ i (a i) : ℝ) : ℂ) * F a) =
      ∑ u : CopyScheduleY role n → A,
        ((∏ y, μ (scheduledOutputVertex role n (.inr y)) (u y) : ℝ) : ℂ) *
        ∑ l : CopyScheduleH role n → A,
          ((∏ h, μ (scheduledOutputVertex role n (.inl (true, h))) (l h) : ℝ) : ℂ) *
          ∑ r : CopyScheduleH role n → A,
            ((∏ h, μ (scheduledOutputVertex role n (.inl (false, h))) (r h) : ℝ) : ℂ) *
              F (scheduledCopiedAssignment role n u l r) := by
  rw [← (scheduledCopiedAssignmentEquiv (A := A) role n).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  change ((∏ i, μ i (scheduledCopiedAssignment role n u l r i) : ℝ) : ℂ) * _ = _
  rw [scheduledCopiedAssignment_prior]
  change _ * F (scheduledCopiedAssignment role n u l r) = _
  push_cast
  ring

end Ostmann

end OAI
