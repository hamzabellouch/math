import OAI.NumberTheory.Ostmann.Construction.FixedPivotEnergyTransport
import OAI.NumberTheory.Ostmann.Construction.ConstituentPriorAssembly

namespace OAI

/-! # Exact H/Y marginal after fixing the composite pivot -/

namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_prior_fubini_real {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (μ : CopyScheduleAtoms role n → A → ℝ) (F : (CopyScheduleAtoms role n → A) → ℝ) :
    (∑ q, (∏ i, μ i (q i)) * F q) =
      ∑ u : CopyScheduleY role n → A,
        (∏ y, μ (enumeratedPartitionEquiv role n r e (.inr (.inr y))) (u y)) *
        ∑ x : Fin r → A,
          (∏ i, μ (enumeratedPartitionEquiv role n r e (.inl i)) (x i)) *
          ∑ l : CopyScheduleH role n → A,
            (∏ h, μ (enumeratedPartitionEquiv role n r e (.inr (.inl h))) (l h)) *
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
  change (∏ i, μ i (scheduledPartitionAssignment role n r e u x l i)) *
    F (scheduledPartitionAssignment role n r e u x l) = _
  rw [scheduledPartitionAssignment_prior]
  ring

/-- Every pivot constituent is integrated out, leaving one copy of each H/Y law. -/
theorem constituent_fixedPivot_prior_fubini {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n M : ℕ) (p : I)
    (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (μ : SurvivingConstituent role size n → P → ℝ)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (F : D → (CopyScheduleAtoms role n → ℕ) → ℝ) :
    (∑ d, ∑ q : SurvivingConstituent role size n → P,
      (∏ i, μ i (q i)) * F d (scheduledReplacePivot role n M
        (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod))) =
    let e := pivotConstituentEquiv role size n p hp hu
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    ∑ u : CopyScheduleY ρ n → P,
      (∏ y, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inr y))) (u y)) *
      ∑ l : CopyScheduleH ρ n → P,
        (∏ h, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inl h))) (l h)) *
        ∑ d, F d (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let e := pivotConstituentEquiv role size n p hp hu
  have hgroup (u : CopyScheduleY ρ n → P) (x : Fin (size p) → P)
      (l : CopyScheduleH ρ n → P) :
      scheduledReplacePivot role n M
        (fun a => ((scheduleConstituentWord role size n a).map
          (fun v => ((scheduledPartitionAssignment (A := P) ρ n (size p) e u x l v : P) : ℕ))).prod) =
        scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ)) := by
    have hmap := scheduledPartitionAssignment_map ρ n (size p) e (fun a : P => (a : ℕ)) u x l
    simp_rw [congrFun hmap]
    rw [constituent_partition_assignment role size n p hp hu]
    rw [scheduledReplacePivot_eq_inserted]
    simp_rw [scheduledInsertedAtoms_H, scheduledInsertedAtoms_Y]
    rfl
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hF := scheduled_prior_fubini_real ρ n (size p) e μ
    (fun q => ∑ d, F d (scheduledReplacePivot role n M
      (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod)))
  refine hF.trans ?_
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  have hm : (∑ x : Fin (size p) → P,
      ∏ k, μ (enumeratedPartitionEquiv ρ n (size p) e (.inl k)) (x k)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  simp_rw [hgroup]
  rw [← Finset.sum_mul, hm, one_mul]

end Ostmann

end OAI
