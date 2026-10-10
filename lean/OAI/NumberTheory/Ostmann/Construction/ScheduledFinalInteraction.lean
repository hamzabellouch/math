import OAI.NumberTheory.Ostmann.Construction.ScheduledMatchedEdges
import OAI.NumberTheory.Ostmann.Construction.SignedAtomSchedule

namespace OAI

/-! # Every distinct final pair has a genuine one-sided scheduled interaction -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledPairMatching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e f : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleH role (n + 1)) :=
  (scheduledFinalPerm role n m word f).symm.trans (scheduledFinalPerm role n m word e)

/-- The two final reassignments induce this literal matching of retained
prime slots. The short modulus is one of the constructed outside anchors. -/
theorem scheduled_final_pair_interaction {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (h : CopyScheduleH role (n + 1)) (j : Fin (n + 1)) (b : Bool),
      let a := scheduledPastAnchor role n (anchor j) j (ha j) b
      let G := scheduledMatchedGraph role pivot (n + 1) (scheduledPairMatching role n m word e f)
      (G (.inr a) (.inl h) = 2 ∨ G (.inr a) (.inl h) = -2) ∧
        G (.inl h) (.inr a) = 0 := by
  obtain ⟨x, hx⟩ := distinct_reassignments_change_code (fun _ => 1)
    (fun _ => Or.inl rfl) e f hef
  let h := scheduledWordH role (n + 1) (parityPathValue (paritySlotPerm e x).1)
    (word (paritySlotPerm e x).2)
  have he : scheduledFinalPerm role n m word e
      (scheduledWordH role (n + 1) (parityPathValue x.1) (word x.2)) = h :=
    scheduledFinalPerm_word role n m word e x
  have hf : (scheduledPairMatching role n m word e f).symm h =
      scheduledWordH role (n + 1) (parityPathValue (paritySlotPerm f x).1)
        (word (paritySlotPerm f x).2) := by
    change scheduledFinalPerm role n m word f ((scheduledFinalPerm role n m word e).symm h) = _
    rw [← he, Equiv.symm_apply_apply]
    exact scheduledFinalPerm_word role n m word f x
  have hpath : ((scheduledPairMatching role n m word e f).symm h).val =
      copySchedulePath (n + 1) (parityPathValue (paritySlotPerm f x).1)
        (word (paritySlotPerm f x).2).val := by
    rw [hf]
    rfl
  have hparity := (paritySlotPerm_preserves_parity e x).trans
    (paritySlotPerm_preserves_parity f x).symm
  obtain ⟨j, b, hj⟩ := scheduledMatchedGraph_changed_code role pivot n
    (scheduledPairMatching role n m word e f) anchor ha hp
    (word (paritySlotPerm e x).2).val (word (paritySlotPerm f x).2).val
    (word (paritySlotPerm e x).2).property (word (paritySlotPerm f x).2).property
    (parityPathValue (paritySlotPerm e x).1) (parityPathValue (paritySlotPerm f x).1)
    h rfl hpath hparity hx
  exact ⟨h, j, b, hj⟩

/-- The matching also preserves the original role, so it preserves both
its character and its unconditioned harmonic marginal. -/
theorem scheduledPairMatching_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e f : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1)) :
    copyScheduleOrigin (n + 1) (scheduledPairMatching role n m word e f h).val =
      copyScheduleOrigin (n + 1) h.val := by
  change copyScheduleOrigin (n + 1)
    (scheduledFinalPerm role n m word e ((scheduledFinalPerm role n m word f).symm h)).val = _
  rw [scheduledFinalPerm_origin]
  have hh := scheduledFinalPerm_origin role n m word f
    ((scheduledFinalPerm role n m word f).symm h)
  rw [Equiv.apply_symm_apply] at hh
  exact hh.symm

theorem scheduled_final_pair_nonprincipal {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (χ : (CopyScheduleH role (n + 1) ⊕ CopyScheduleY role (n + 1)) →
      ∀ p : ℕ, DirichletCharacter ℂ p)
    (Q : (CopyScheduleH role (n + 1) ⊕ CopyScheduleY role (n + 1)) → Finset ℕ)
    (hsquare : ∀ j b q, q ∈ Q (.inr (scheduledPastAnchor role n (anchor j) j (ha j) b)) →
      χ (.inr (scheduledPastAnchor role n (anchor j) j (ha j) b)) q ^ 2 ≠ 1)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (a v : CopyScheduleH role (n + 1) ⊕ CopyScheduleY role (n + 1)),
      a ≠ v ∧
      (∀ q ∈ Q a, χ a q ^
        scheduledMatchedGraph role pivot (n + 1) (scheduledPairMatching role n m word e f) a v ≠ 1) ∧
      scheduledMatchedGraph role pivot (n + 1) (scheduledPairMatching role n m word e f) v a = 0 := by
  obtain ⟨h, j, b, hfwd, hrev⟩ := scheduled_final_pair_interaction role pivot n m word
    anchor ha hp e f hef
  exact ⟨.inr (scheduledPastAnchor role n (anchor j) j (ha j) b), .inl h,
    (by simp), (fun q hq => signed_square_nonprincipal _ (hsquare j b q hq) _ hfwd), hrev⟩

end Ostmann

end OAI
