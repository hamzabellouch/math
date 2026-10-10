import OAI.NumberTheory.Ostmann.Construction.ScheduledSampleQuotient
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalInteraction

namespace OAI

/-! # The retained anchor interaction inside the full surviving-prime graph -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledHMatching {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) : Equiv.Perm (CopyScheduleAtoms role n) :=
  ((scheduleHSurvivorEquiv role n).permCongr e).subtypeCongr (Equiv.refl _)

noncomputable def scheduledRetainedEmbedding {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    (CopyScheduleH role n ⊕ CopyScheduleY role n) ↪ CopyScheduleAtoms role n :=
  ⟨fun z => scheduledPartitionEquiv role n (.inr z), by
    intro x y h
    exact Sum.inr.inj ((scheduledPartitionEquiv role n).injective h)⟩

theorem scheduledHMatching_active {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) (h : CopyScheduleH role n) :
    scheduledHMatching role n e ⟨h.val, h.property.1⟩ = ⟨(e h).val, (e h).property.1⟩ := by
  exact Equiv.Perm.subtypeCongr.left_apply_subtype
    ((scheduleHSurvivorEquiv role n).permCongr e) (Equiv.refl _)
    (scheduleHSurvivorEquiv role n h)

theorem scheduledHMatching_inactive {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) (q : CopyScheduleAtoms role n)
    (hq : (copyScheduleRole role n q.val).copiedAt n ≠ true) :
    scheduledHMatching role n e q = q := by
  unfold scheduledHMatching
  simp only [Equiv.Perm.subtypeCongr.apply, dite_eq_right hq, Equiv.refl_apply]

theorem scheduledHMatching_retained {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) (z : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    scheduledHMatching role n e (scheduledRetainedEmbedding role n z) =
      scheduledRetainedEmbedding role n (Equiv.sumCongr e (Equiv.refl _) z) := by
  cases z with
  | inl h => exact scheduledHMatching_active role n e h
  | inr y =>
    apply scheduledHMatching_inactive
    change (copyScheduleRole role n y.val).copiedAt n ≠ true
    rw [y.property.2.1]
    decide

theorem scheduledHMatching_symm_retained {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) (z : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    (scheduledHMatching role n e).symm (scheduledRetainedEmbedding role n z) =
      scheduledRetainedEmbedding role n ((Equiv.sumCongr e (Equiv.refl _)).symm z) := by
  apply (scheduledHMatching role n e).injective
  rw [Equiv.apply_symm_apply, scheduledHMatching_retained, Equiv.apply_symm_apply]

theorem scheduledHMatching_graph {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role n))
    (z w : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    graphDifference (scheduledSurvivorGraph role pivot n)
      (transportGraph (scheduledHMatching role n e) (scheduledSurvivorGraph role pivot n))
      (scheduledRetainedEmbedding role n z) (scheduledRetainedEmbedding role n w) =
        scheduledMatchedGraph role pivot n e z w := by
  have hb (u v : CopyScheduleH role n ⊕ CopyScheduleY role n) :
      scheduledSurvivorGraph role pivot n (scheduledRetainedEmbedding role n u)
        (scheduledRetainedEmbedding role n v) =
      retainedInternalGraph (scheduledRetainedGraph role initialCompleteGraph pivot n) u v := by
    cases u <;> cases v <;> rfl
  change scheduledSurvivorGraph role pivot n (scheduledRetainedEmbedding role n z)
      (scheduledRetainedEmbedding role n w) -
    scheduledSurvivorGraph role pivot n
      ((scheduledHMatching role n e).symm (scheduledRetainedEmbedding role n z))
      ((scheduledHMatching role n e).symm (scheduledRetainedEmbedding role n w)) = _
  rw [scheduledHMatching_symm_retained, scheduledHMatching_symm_retained, hb, hb]
  rfl

theorem scheduledHMatching_symm {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) :
    (scheduledHMatching role n e).symm = scheduledHMatching role n e.symm := rfl

theorem scheduledHMatching_trans {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e f : Equiv.Perm (CopyScheduleH role n)) :
    (scheduledHMatching role n e).trans (scheduledHMatching role n f) =
      scheduledHMatching role n (e.trans f) := by
  unfold scheduledHMatching
  rw [Equiv.Perm.subtypeCongr.trans, Equiv.permCongr_trans]
  rfl

theorem paritySlotPerm_inv {n m : ℕ} (e : FinalParityReassignments n m) :
    paritySlotPerm (e⁻¹) = (paritySlotPerm e).symm := by
  apply Equiv.ext
  rintro ⟨path, i⟩
  cases path <;> rfl

theorem scheduledFinalPerm_inv {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) :
    scheduledFinalPerm role n m word (e⁻¹) = (scheduledFinalPerm role n m word e).symm := by
  unfold scheduledFinalPerm
  rw [paritySlotPerm_inv]
  rfl

theorem scheduledFullFinalPerm_matching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e f : FinalParityReassignments n m) :
    (scheduledFullFinalPerm role n m word f).trans (scheduledFullFinalPerm role n m word e).symm =
      scheduledHMatching role (n + 1) (scheduledPairMatching role n m word (e⁻¹) (f⁻¹)) := by
  change (scheduledHMatching role (n + 1) (scheduledFinalPerm role n m word f)).trans
    (scheduledHMatching role (n + 1) (scheduledFinalPerm role n m word e)).symm = _
  rw [scheduledHMatching_symm, scheduledHMatching_trans]
  unfold scheduledPairMatching
  rw [scheduledFinalPerm_inv, scheduledFinalPerm_inv, Equiv.symm_symm]

theorem scheduled_full_matching_one_sided {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ a b : CopyScheduleAtoms role (n + 1), a ≠ b ∧
      (let G := graphDifference (scheduledSurvivorGraph role pivot (n + 1))
        (transportGraph (scheduledHMatching role (n + 1) (scheduledPairMatching role n m word e f))
          (scheduledSurvivorGraph role pivot (n + 1)))
       (G a b = 2 ∨ G a b = -2) ∧ G b a = 0) := by
  obtain ⟨h, j, sign, hfwd, hrev⟩ :=
    scheduled_final_pair_interaction role pivot n m word anchor ha hp e f hef
  let a := scheduledPastAnchor role n (anchor j) j (ha j) sign
  refine ⟨scheduledRetainedEmbedding role (n + 1) (.inr a),
    scheduledRetainedEmbedding role (n + 1) (.inl h), ?_, ?_⟩
  · exact (scheduledRetainedEmbedding role (n + 1)).injective.ne (by simp)
  · dsimp only
    rw [scheduledHMatching_graph, scheduledHMatching_graph]
    exact ⟨hfwd, hrev⟩

end Ostmann

end OAI
