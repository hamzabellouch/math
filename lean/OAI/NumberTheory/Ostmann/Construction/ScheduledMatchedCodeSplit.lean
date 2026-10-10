import OAI.NumberTheory.Ostmann.Construction.ScheduledMatchedEdges

namespace OAI

/-! # Both parity cases for the actual code-changing matching -/
namespace Ostmann
open scoped Classical

/-- A changed code chooses either the small-anchor-to-word character or the
word-to-large-anchor character. The same computed graph is used in both cases. -/
theorem scheduledMatchedGraph_changed_code_split {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (small large : Fin (n + 1) → I)
    (hsmall : ∀ j, role (small j) = .anchor j) (hlarge : ∀ j, role (large j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (i i' : I) (hi : role i = .word) (hi' : role i' = .word)
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i')
    (hcode : finiteAnchorCode (fun _ => 1) t ≠ finiteAnchorCode (fun _ => 1) t') :
    ∃ (j : Fin (n + 1)) (b : Bool),
      let a := scheduledPastAnchor role n (small j) j (hsmall j) b
      let a' := scheduledPastAnchor role n (large j) j (hlarge j) b
      let G := scheduledMatchedGraph role pivot (n + 1) e
      ((G (.inr a) (.inl h) = 2 ∨ G (.inr a) (.inl h) = -2) ∧ G (.inl h) (.inr a) = 0) ∨
      ((G (.inl h) (.inr a') = 2 ∨ G (.inl h) (.inr a') = -2) ∧ G (.inr a') (.inl h) = 0) := by
  obtain ⟨j, b, hj⟩ := distinct_anchor_code_entry (fun _ => 1) t t' hcode
  have hs (u : Fin (n + 1) → Bool) : finalCopyParity u = 1 ∨ finalCopyParity u = -1 :=
    copyPathParity_sign (finiteCopyPath u) (n + 1)
  have hsign (u : Fin (n + 1) → Bool) :
      anchorCodeEntry (fun _ => 1) u j b = 1 ∨ anchorCodeEntry (fun _ => 1) u j b = -1 :=
    anchorCodeEntry_sign (fun _ => 1) (fun _ => Or.inl rfl) u j b
  have hsep (a : I) (ha : role a = .anchor j) :
      (∀ k < n + 1, a ≠ pivot k) ∧ a ≠ i ∧ a ≠ i' := by
    constructor
    · intro k hk he
      have he' := congrArg role he
      rw [ha, hp k hk] at he'
      cases he'
    · constructor
      · intro he
        have he' := congrArg role he
        rw [ha, hi] at he'
        cases he'
      · intro he
        have he' := congrArg role he
        rw [ha, hi'] at he'
        cases he'
  have hip : ∀ k < n + 1, i ≠ pivot k := by
    intro k hk he
    have he' := congrArg role he
    rw [hi, hp k hk] at he'
    cases he'
  have hi'p : ∀ k < n + 1, i' ≠ pivot k := by
    intro k hk he
    have he' := congrArg role he
    rw [hi', hp k hk] at he'
    cases he'
  have hsf := scheduledMatchedGraph_anchor_word role pivot n e (small j) i i' j (hsmall j) b
    (hsep _ (hsmall j)).1 (hsep _ (hsmall j)).2.1 (hsep _ (hsmall j)).2.2 t t' h hh hh'
  have hsr := scheduledMatchedGraph_word_anchor role pivot n e (small j) i i' j (hsmall j) b
    hip hi'p (hsep _ (hsmall j)).2.1.symm (hsep _ (hsmall j)).2.2.symm t t' h hh hh'
  have hlf := scheduledMatchedGraph_anchor_word role pivot n e (large j) i i' j (hlarge j) b
    (hsep _ (hlarge j)).1 (hsep _ (hlarge j)).2.1 (hsep _ (hlarge j)).2.2 t t' h hh hh'
  have hlr := scheduledMatchedGraph_word_anchor role pivot n e (large j) i i' j (hlarge j) b
    hip hi'p (hsep _ (hlarge j)).2.1.symm (hsep _ (hlarge j)).2.2.symm t t' h hh hh'
  refine ⟨j, b, ?_⟩
  dsimp only
  rcases changed_anchor_code_one_sided _ _ _ _ (hs t) (hs t') (hsign t) (hsign t') hj with hf | hr
  · apply Or.inl
    rw [hsf, hsr]
    exact hf
  · apply Or.inr
    rw [hlr, hlf]
    exact ⟨hr.2, hr.1⟩

end Ostmann

end OAI
