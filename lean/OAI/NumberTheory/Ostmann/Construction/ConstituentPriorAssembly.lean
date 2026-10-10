import OAI.NumberTheory.Ostmann.Construction.ConstituentPartitionAssignment
import OAI.NumberTheory.Ostmann.Construction.FullCopiedWeight

namespace OAI

/-! # Exact original-prior assembly of the full constituent Fourier weight -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledPartitionAssignment_map {I A B : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (f : A → B) (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A) :
    (fun i => f (scheduledPartitionAssignment role n r e u x l i)) =
      scheduledPartitionAssignment role n r e (f ∘ u) (f ∘ x) (f ∘ l) := by
  funext i
  obtain ⟨j, rfl⟩ := (enumeratedPartitionEquiv role n r e).surjective i
  simp only [scheduledPartitionAssignment_apply]
  rcases j with k | h | y <;> rfl

/-- The pivot tuple and both remaining coordinate blocks keep their original
marginals. The full coefficient depends on the pivot tuple only through its
product, as required by the arithmetic Cauchy step. -/
theorem constituent_weighted_prior_fubini {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I)
    (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (μ : SurvivingConstituent role size n → P → ℝ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (phase : (SurvivingConstituent role size n → P) → D → ℂ) :
    (∑ q : SurvivingConstituent role size n → P, ((∏ i, μ i (q i) : ℝ) : ℂ) *
      ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod)
        (hist d) * phase q d) =
    let e := pivotConstituentEquiv role size n p hp hu
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    ∑ u : CopyScheduleY ρ n → P,
      ((∏ y, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inr y))) (u y) : ℝ) : ℂ) *
      ∑ x : Fin (size p) → P,
        ((∏ k, μ (enumeratedPartitionEquiv ρ n (size p) e (.inl k)) (x k) : ℝ) : ℂ) *
        ∑ l : CopyScheduleH ρ n → P,
          ((∏ h, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inl h))) (l h) : ℝ) : ℂ) *
          ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
            (scheduledInsertedAtoms role n (∏ k, (x k : ℕ))
              (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
              (fun y => ∏ k, (u (constituentY role size n y k) : ℕ)))
            (hist d) * phase (scheduledPartitionAssignment ρ n (size p) e u x l) d := by
  dsimp only
  have hF := scheduled_prior_fubini (fun i : Σ a, Fin (size a) => role i.1)
    n (size p) (pivotConstituentEquiv role size n p hp hu) μ
    (fun q => ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod)
      (hist d) * phase q d)
  refine hF.trans ?_
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  have hmap := scheduledPartitionAssignment_map
    (fun i : Σ a, Fin (size a) => role i.1) n (size p)
    (pivotConstituentEquiv role size n p hp hu) (fun q : P => (q : ℕ)) u x l
  have hg := constituent_partition_assignment role size n p hp hu
    (fun y => (u y : ℕ)) (fun k => (x k : ℕ)) (fun h => (l h : ℕ))
  have hg' : (fun v => ((scheduleConstituentWord role size n v).map
      (fun i => ((scheduledPartitionAssignment (A := P) _ n (size p)
        (pivotConstituentEquiv role size n p hp hu) u x l i : P) : ℕ))).prod) =
      scheduledInsertedAtoms role n (∏ k, (x k : ℕ))
        (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ)) := by
    rw [hmap]
    exact hg
  rw [hg']

end Ostmann

end OAI
