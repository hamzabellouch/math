import OAI.NumberTheory.Ostmann.Construction.ConstituentPairFactors
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalPermutation

namespace OAI

/-! # The anchor interaction in the literal retained matching graph -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledMatchedGraph {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role n)) :
    (CopyScheduleH role n ⊕ CopyScheduleY role n) →
      (CopyScheduleH role n ⊕ CopyScheduleY role n) → ℤ :=
  let g := retainedInternalGraph (scheduledRetainedGraph role initialCompleteGraph pivot n)
  graphDifference g (transportGraph (Equiv.sumCongr e (Equiv.refl _)) g)

theorem constituentMatchedGraph_eq {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (pivot : ℕ → (Σ i, Fin (size i))) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ j, Fin (size j) => role i.1) n)) :
    constituentMatchedGraph role size pivot n e =
      scheduledMatchedGraph (fun i : Σ j, Fin (size j) => role i.1) pivot n e := rfl

theorem scheduledMatchedGraph_self {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role n))
    (x : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    scheduledMatchedGraph role pivot n e x x = 0 := by
  simp only [scheduledMatchedGraph, graphDifference, transportGraph, retainedInternalGraph,
    scheduledRetainedGraph_diagonal, sub_self]

theorem scheduledMatchedGraph_outside {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role n))
    (a b : CopyScheduleY role n) :
    scheduledMatchedGraph role pivot n e (.inr a) (.inr b) = 0 := by
  simp only [scheduledMatchedGraph, graphDifference, transportGraph,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_symm,
    Equiv.refl_apply, sub_self]

noncomputable def scheduledPastAnchor {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (a : I) (j : Fin (n + 1)) (ha : role a = .anchor j) (b : Bool) :
    CopyScheduleY role (n + 1) :=
  ⟨copyScheduleAnchor (n + 1) j b a,
    copyScheduleSurvives_anchor role a j ha (n + 1) j.isLt b, by
      rw [copyScheduleRole_anchor role a j ha (n + 1) j.isLt b]
      exact ⟨rfl, rfl⟩⟩

/-- This is an identity for the computed graph, with the counterpart slot
identified by the actual inverse matching permutation. -/
theorem scheduledMatchedGraph_anchor_word {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (a i i' : I) (j : Fin (n + 1)) (ha : role a = .anchor j) (b : Bool)
    (hap : ∀ k < n + 1, a ≠ pivot k) (hai : a ≠ i) (hai' : a ≠ i')
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i') :
    scheduledMatchedGraph role pivot (n + 1) e
      (.inr (scheduledPastAnchor role n a j ha b)) (.inl h) =
      anchorIncoming (fun _ => 1) t j b - anchorIncoming (fun _ => 1) t' j b := by
  change copyScheduleGraph initialCompleteGraph pivot (n + 1)
      (copyScheduleAnchor (n + 1) j b a) h.val -
    copyScheduleGraph initialCompleteGraph pivot (n + 1)
      (copyScheduleAnchor (n + 1) j b a) (e.symm h).val = _
  rw [hh, hh', copyScheduleGraph_anchor_to_path, copyScheduleGraph_anchor_to_path]
  · exact fun k hk => initialCompleteGraph_of_ne (hap k hk)
  · exact initialCompleteGraph_of_ne hai'
  · exact fun k hk => initialCompleteGraph_of_ne (hap k hk)
  · exact initialCompleteGraph_of_ne hai

theorem scheduledMatchedGraph_word_anchor {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (a i i' : I) (j : Fin (n + 1)) (ha : role a = .anchor j) (b : Bool)
    (hip : ∀ k < n + 1, i ≠ pivot k) (hi'p : ∀ k < n + 1, i' ≠ pivot k)
    (hia : i ≠ a) (hi'a : i' ≠ a)
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i') :
    scheduledMatchedGraph role pivot (n + 1) e
      (.inl h) (.inr (scheduledPastAnchor role n a j ha b)) =
      finalCopyParity t - finalCopyParity t' := by
  change copyScheduleGraph initialCompleteGraph pivot (n + 1)
      h.val (copyScheduleAnchor (n + 1) j b a) -
    copyScheduleGraph initialCompleteGraph pivot (n + 1)
      (e.symm h).val (copyScheduleAnchor (n + 1) j b a) = _
  rw [hh, hh', copyScheduleGraph_path_to_anchor, copyScheduleGraph_path_to_anchor]
  · exact fun k hk => initialCompleteGraph_of_ne (hi'p k hk)
  · exact initialCompleteGraph_of_ne hi'a
  · exact j.isLt
  · exact fun k hk => initialCompleteGraph_of_ne (hip k hk)
  · exact initialCompleteGraph_of_ne hia
  · exact j.isLt

/-- A changed code with unchanged final parity supplies a genuine signed
square in the actual matching graph. All other graph entries remain arbitrary. -/
theorem scheduledMatchedGraph_changed_code {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (i i' : I) (hi : role i = .word) (hi' : role i' = .word)
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i')
    (hparity : finalCopyParity t = finalCopyParity t')
    (hcode : finiteAnchorCode (fun _ => 1) t ≠ finiteAnchorCode (fun _ => 1) t') :
    ∃ (j : Fin (n + 1)) (b : Bool),
      let a := scheduledPastAnchor role n (anchor j) j (ha j) b
      let G := scheduledMatchedGraph role pivot (n + 1) e
      (G (.inr a) (.inl h) = 2 ∨ G (.inr a) (.inl h) = -2) ∧
        G (.inl h) (.inr a) = 0 := by
  obtain ⟨j, b, hj⟩ := distinct_anchor_code_entry (fun _ => 1) t t' hcode
  have hs (u : Fin (n + 1) → Bool) : finalCopyParity u = 1 ∨ finalCopyParity u = -1 :=
    copyPathParity_sign (finiteCopyPath u) (n + 1)
  have hsign (u : Fin (n + 1) → Bool) :
      anchorCodeEntry (fun _ => 1) u j b = 1 ∨
        anchorCodeEntry (fun _ => 1) u j b = -1 :=
    anchorCodeEntry_sign (fun _ => 1) (fun _ => Or.inl rfl) u j b
  have hf : anchorIncoming (fun _ => 1) t j b - anchorIncoming (fun _ => 1) t' j b = 2 ∨
      anchorIncoming (fun _ => 1) t j b - anchorIncoming (fun _ => 1) t' j b = -2 := by
    rcases changed_anchor_code_one_sided _ _ _ _ (hs t) (hs t')
      (hsign t) (hsign t') hj with hx | hx
    · exact hx.1
    · have hz : finalCopyParity t - finalCopyParity t' = 0 := sub_eq_zero.mpr hparity
      rcases hx.2 with hx | hx <;> omega
  have hap : ∀ k < n + 1, anchor j ≠ pivot k := by
    intro k hk he
    have he' := congrArg role he
    rw [ha j, hp k hk] at he'
    cases he'
  have hai : anchor j ≠ i := by
    intro he
    have he' := congrArg role he
    rw [ha j, hi] at he'
    cases he'
  have hai' : anchor j ≠ i' := by
    intro he
    have he' := congrArg role he
    rw [ha j, hi'] at he'
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
  refine ⟨j, b, ?_⟩
  dsimp only
  rw [scheduledMatchedGraph_anchor_word role pivot n e (anchor j) i i' j (ha j) b
    hap hai hai' t t' h hh hh',
    scheduledMatchedGraph_word_anchor role pivot n e (anchor j) i i' j (ha j) b
      hip hi'p hai.symm hai'.symm t t' h hh hh']
  exact ⟨hf, sub_eq_zero.mpr hparity⟩

end Ostmann

end OAI
