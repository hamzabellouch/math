import OAI.NumberTheory.Ostmann.Construction.EnumeratedSchedulePhase
import OAI.NumberTheory.Ostmann.Construction.FiniteProductPrior

namespace OAI

/-! # Exact decomposition of the original prior at a scheduled pivot -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledPartitionAssignment {I A : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A) :
    {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A :=
  fun i => Sum.elim x (Sum.elim l u) ((enumeratedPartitionEquiv role n r e).symm i)

theorem scheduledPartitionAssignment_apply {I A : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A)
    (j : Fin r ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n)) :
    scheduledPartitionAssignment role n r e u x l (enumeratedPartitionEquiv role n r e j) =
      Sum.elim x (Sum.elim l u) j := by
  simp only [scheduledPartitionAssignment, Equiv.symm_apply_apply]

noncomputable def scheduledPartitionAssignmentEquiv {I A : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) :
    ((CopyScheduleY role n → A) × ((Fin r → A) × (CopyScheduleH role n → A))) ≃
      ({i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A) where
  toFun a := scheduledPartitionAssignment role n r e a.1 a.2.1 a.2.2
  invFun a := ((fun y => a (enumeratedPartitionEquiv role n r e (.inr (.inr y)))),
    (fun i => a (enumeratedPartitionEquiv role n r e (.inl i))),
    (fun h => a (enumeratedPartitionEquiv role n r e (.inr (.inl h)))))
  left_inv a := by
    apply Prod.ext
    · funext y
      exact scheduledPartitionAssignment_apply role n r e a.1 a.2.1 a.2.2 (.inr (.inr y))
    · apply Prod.ext
      · funext i
        exact scheduledPartitionAssignment_apply role n r e a.1 a.2.1 a.2.2 (.inl i)
      · funext h
        exact scheduledPartitionAssignment_apply role n r e a.1 a.2.1 a.2.2 (.inr (.inl h))
  right_inv a := by
    funext j
    obtain ⟨i, rfl⟩ := (enumeratedPartitionEquiv role n r e).surjective j
    dsimp only
    rw [scheduledPartitionAssignment_apply]
    rcases i with i | h | y <;> rfl

/-- The retained outside prior occurs once, while the pivot and H priors
stay in their own independent blocks. -/
theorem scheduledPartitionAssignment_prior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (μ : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A → ℝ)
    (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A) :
    (∏ i, μ i (scheduledPartitionAssignment role n r e u x l i)) =
      (∏ y, μ (enumeratedPartitionEquiv role n r e (.inr (.inr y))) (u y)) *
      (∏ i, μ (enumeratedPartitionEquiv role n r e (.inl i)) (x i)) *
      (∏ h, μ (enumeratedPartitionEquiv role n r e (.inr (.inl h))) (l h)) := by
  rw [← (enumeratedPartitionEquiv role n r e).prod_comp]
  simp only [scheduledPartitionAssignment_apply, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  ring

/-- This is the precise finite Fubini identity used by the current amplitude;
it changes no marginal, including the common outside sample. -/
theorem scheduled_prior_fubini {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (μ : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A → ℝ)
    (F : ({i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A) → ℂ) :
    (∑ a, ((∏ i, μ i (a i) : ℝ) : ℂ) * F a) =
      ∑ u : CopyScheduleY role n → A,
        ((∏ y, μ (enumeratedPartitionEquiv role n r e (.inr (.inr y))) (u y) : ℝ) : ℂ) *
        ∑ x : Fin r → A,
          ((∏ i, μ (enumeratedPartitionEquiv role n r e (.inl i)) (x i) : ℝ) : ℂ) *
          ∑ l : CopyScheduleH role n → A,
            ((∏ h, μ (enumeratedPartitionEquiv role n r e (.inr (.inl h))) (l h) : ℝ) : ℂ) *
              F (scheduledPartitionAssignment role n r e u x l) := by
  rw [← (scheduledPartitionAssignmentEquiv (A := A) role n r e).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  change ((∏ i, μ i (scheduledPartitionAssignment role n r e u x l i) : ℝ) : ℂ) * _ = _
  rw [scheduledPartitionAssignment_prior]
  change _ * F (scheduledPartitionAssignment role n r e u x l) = _
  push_cast
  ring

end Ostmann

end OAI
