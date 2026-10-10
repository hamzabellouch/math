import OAI.NumberTheory.Ostmann.Tree.BadArrangementCount

namespace OAI

/-! # Counting bad bulk matchings while retaining every nonbulk slot -/

namespace Ostmann
open scoped Classical

def sumSide {A B : Type*} : A ⊕ B → Bool := Sum.elim (fun _ => true) (fun _ => false)

noncomputable def sumSideLeftEquiv (A B : Type*) :
    A ≃ {x : A ⊕ B // sumSide x = true} :=
  Equiv.ofBijective (fun a => ⟨Sum.inl a, rfl⟩) (by
    constructor
    · intro a b h; exact Sum.inl.inj (congrArg Subtype.val h)
    · rintro ⟨a | b, h⟩
      · exact ⟨a, rfl⟩
      · cases h)

noncomputable def sumSideRightEquiv (A B : Type*) :
    B ≃ {x : A ⊕ B // sumSide x = false} :=
  Equiv.ofBijective (fun b => ⟨Sum.inr b, rfl⟩) (by
    constructor
    · intro a b h; exact Sum.inr.inj (congrArg Subtype.val h)
    · rintro ⟨a | b, h⟩
      · cases h
      · exact ⟨b, rfl⟩)

noncomputable def separatedMatchingLeft {A B : Type*}
    (e : PartitionMatching (@sumSide A B) (@sumSide A B)) : Equiv.Perm A :=
  ((sumSideLeftEquiv A B).trans (e.restrict true)).trans (sumSideLeftEquiv A B).symm

noncomputable def separatedMatchingRight {A B : Type*}
    (e : PartitionMatching (@sumSide A B) (@sumSide A B)) : Equiv.Perm B :=
  ((sumSideRightEquiv A B).trans (e.restrict false)).trans (sumSideRightEquiv A B).symm

theorem separatedMatching_pair_injective {A B : Type*} :
    Function.Injective (fun e : PartitionMatching (@sumSide A B) (@sumSide A B) =>
      (separatedMatchingLeft e, separatedMatchingRight e)) := by
  intro e f h
  apply PartitionMatching.restrict_injective
  funext side
  apply Equiv.ext
  intro x
  cases side with
  | false =>
    obtain ⟨b, rfl⟩ := (sumSideRightEquiv A B).surjective x
    have he := congrArg (fun z => (sumSideRightEquiv A B) (z.2 b)) h
    simpa only [separatedMatchingRight, Equiv.trans_apply, Equiv.apply_symm_apply] using he
  | true =>
    obtain ⟨a, rfl⟩ := (sumSideLeftEquiv A B).surjective x
    have he := congrArg (fun z => (sumSideLeftEquiv A B) (z.1 a)) h
    simpa only [separatedMatchingLeft, Equiv.trans_apply, Equiv.apply_symm_apply] using he

/-- Nonbulk slots are still labeled. Their complete permutation cost is a
fixed factorial; all growing bulk multiplicity uses the sharp bad count. -/
theorem bad_separated_matching_count {r m : ℕ} {N : Type*} [Fintype N] :
    Fintype.card {e : PartitionMatching (@sumSide (Fin r × Fin m) N) (@sumSide (Fin r × Fin m) N) //
      BadBulkArrangement (separatedMatchingLeft e)} ≤
      Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} *
        (Fintype.card N).factorial := by
  let f : {e : PartitionMatching (@sumSide (Fin r × Fin m) N) (@sumSide (Fin r × Fin m) N) //
      BadBulkArrangement (separatedMatchingLeft e)} →
      {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} × Equiv.Perm N :=
    fun e => (⟨separatedMatchingLeft e.val, e.property⟩, separatedMatchingRight e.val)
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    apply separatedMatching_pair_injective
    have hl : separatedMatchingLeft e.val = separatedMatchingLeft e'.val :=
      congrArg (fun z => z.1.val) h
    have hr : separatedMatchingRight e.val = separatedMatchingRight e'.val :=
      congrArg Prod.snd h
    exact Prod.ext hl hr
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_perm] using hc

theorem bad_separated_matching_bound {r m : ℕ} {N : Type*} [Fintype N]
    (hr : 1 ≤ r) (hm : 0 < m) :
    (Fintype.card {e : PartitionMatching (@sumSide (Fin r × Fin m) N) (@sumSide (Fin r × Fin m) N) //
      BadBulkArrangement (separatedMatchingLeft e)} : ℝ) ≤
      (((r + 1) * r ^ (2 * r) : ℕ) : ℝ) * (m.factorial : ℝ) ^ r *
        Real.exp ((m : ℝ) * r * (Real.log r + 1) / 4) * (Fintype.card N).factorial := by
  have hc : (Fintype.card {e : PartitionMatching (@sumSide (Fin r × Fin m) N) (@sumSide (Fin r × Fin m) N) //
      BadBulkArrangement (separatedMatchingLeft e)} : ℝ) ≤
      (Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} : ℝ) *
        (Fintype.card N).factorial := by exact_mod_cast (bad_separated_matching_count (N := N))
  exact hc.trans (mul_le_mul_of_nonneg_right (badBulkArrangement_count_bound hr hm) (by positivity))

end Ostmann

end OAI
