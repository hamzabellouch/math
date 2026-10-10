import OAI.NumberTheory.Ostmann.Construction.ScheduledLeafProducts

namespace OAI

namespace Ostmann
open scoped BigOperators Classical

theorem scheduledActualSourceScheme_left_natCast {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (C : CopyScheduleAtoms role n → ℕ)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (p : Fin (2 ^ n - 1) → ℕ) (j : Fin (2 ^ n - 1)) :
    (scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).leftCoefficient
      (fun j => (p j : ℤ)) j =
        ((∏ a : CopyScheduleH role (scheduledNodeLevel n j),
          scheduledNodeValues role n j C p ⟨.inl (false, a.val), a.property⟩ : ℕ) : ℤ) := by
  unfold scheduledActualSourceScheme
  rw [scheduledSourceScheme_left role S n t _ _ _
    (fun j => scheduledNodeHSources_injective role n false j hu), Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro a _
  have he := scheduledNodeSources_eval role n j C p
    ⟨.inl (false, a.val), a.property⟩
  rw [← he]
  change Sum.elim (fun v => (C v : ℤ))
    (fun k => (p (ancestorNodeIndex n j k) : ℤ)) _ = _
  dsimp only [scheduledNodeHSources]
  cases scheduledNodeSources role n j ⟨.inl (false, a.val), a.property⟩ <;> rfl

theorem scheduledActualSourceScheme_right_natCast {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (C : CopyScheduleAtoms role n → ℕ)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (p : Fin (2 ^ n - 1) → ℕ) (j : Fin (2 ^ n - 1)) :
    (scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).rightCoefficient
      (fun j => (p j : ℤ)) j =
        ((∏ a : CopyScheduleH role (scheduledNodeLevel n j),
          scheduledNodeValues role n j C p ⟨.inl (true, a.val), a.property⟩ : ℕ) : ℤ) := by
  unfold scheduledActualSourceScheme
  rw [scheduledSourceScheme_right role S n t _ _ _
    (fun j => scheduledNodeHSources_injective role n true j hu), Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro a _
  have he := scheduledNodeSources_eval role n j C p
    ⟨.inl (true, a.val), a.property⟩
  rw [← he]
  change Sum.elim (fun v => (C v : ℤ))
    (fun k => (p (ancestorNodeIndex n j k) : ℤ)) _ = _
  dsimp only [scheduledNodeHSources]
  cases scheduledNodeSources role n j ⟨.inl (true, a.val), a.property⟩ <;> rfl

/-- Every equation is derived from the valid full arithmetic history. The
fixed coefficients depend on the remaining word factors and ancestor pivots. -/
theorem scheduled_scaled_history_equations {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (i : I) (hi : role i = .word) (S : Finset ℤ) (n : ℕ)
    (C : CopyScheduleAtoms role n → ℕ) (x : TreeLeafIndex n → ℕ)
    (t : FrequencyTree S n)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (hv : ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n C x⟩ (frequencyTreeMap Subtype.val n t)) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n C x⟩ (frequencyTreeMap Subtype.val n t)
    (scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).equations
      (fun j => (((actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm x)).getD j.val (1, 1)).1 : ℤ))
      (fun j => (((actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm x)).getD j.val (1, 1)).2 : ℤ))
      (fun j => (p j : ℤ)) := by
  dsimp only
  intro j
  let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
    ⟨n, wordLeafScale role i hi n C x⟩ (frequencyTreeMap Subtype.val n t)
  have hvj := scheduledNodeValues_valid role childBound pivotBound S n
    (wordLeafScale role i hi n C x) t hv j
  have hr := hvj.relation
  change (singleTreeNodeFrequencies S n t j.val).left *
      ((∏ a : CopyScheduleH role (scheduledNodeLevel n j),
        scheduledNodeValues role n j (wordLeafScale role i hi n C x) p
          ⟨.inl (false, a.val), a.property⟩ : ℕ) : ℤ) -
    (singleTreeNodeFrequencies S n t j.val).right *
      ((∏ a : CopyScheduleH role (scheduledNodeLevel n j),
        scheduledNodeValues role n j (wordLeafScale role i hi n C x) p
          ⟨.inl (true, a.val), a.property⟩ : ℕ) : ℤ) =
      (singleTreeNodeFrequencies S n t j.val).root * (p j : ℤ) at hr
  rw [scheduledNodeValues_H_product, scheduledNodeValues_H_product] at hr
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.cast_mul] at hr
  change (singleTreeNodeFrequencies S n t j.val).left * _ * _ -
    (singleTreeNodeFrequencies S n t j.val).right * _ * _ =
      (singleTreeNodeFrequencies S n t j.val).root * (p j : ℤ)
  rw [scheduledActualSourceScheme_left_natCast role S n t C hu,
    scheduledActualSourceScheme_right_natCast role S n t C hu]
  simpa only [mul_assoc] using hr

end Ostmann

end OAI
