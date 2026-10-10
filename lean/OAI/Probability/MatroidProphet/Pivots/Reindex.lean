import OAI.Probability.MatroidProphet.Pivots.Completeness
import Mathlib.Data.Finset.Sort

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α β γ O A : Type*} [Fintype α]

lemma isPivot_reindex
    {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype α]
    (M : Matroid α) (label : β → α) (time : β → ℕ)
    (e : γ ≃ β) (f : α) (o : γ) :
    IsPivot M (label ∘ e) (time ∘ e) f o ↔ IsPivot M label time f (e o) := by
  have himage (p : β → Prop) : (label ∘ e) '' {x | p (e x)} = label '' {x | p x} := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.symm x, by simpa using hx, by simp⟩
  unfold IsPivot
  simp only [Function.comp_apply] at himage ⊢
  rw [himage (fun x => time x ≤ time (e o)), himage (fun x => time x < time (e o))]

noncomputable def freeMarkedPatterns [Fintype O] [LinearOrder O] [Fintype A]
    (M : Matroid α) (oldLabel : O → α) (movableLabel : A → α)
    {n : ℕ} (test : Fin n → α) (oldMark : O → Bool) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun t => ∃ time : O ⊕ A → ℕ,
    StrictMono (fun o => time (Sum.inl o)) ∧ Function.Injective time ∧
    ∃ mark : A → Bool, ∀ f, ∃ o,
      IsPivot M (Sum.elim oldLabel movableLabel) time (test f) o ∧
        (Sum.elim oldMark mark o = true ↔ f ∈ t)

lemma card_freeMarkedPatterns_le [Fintype O] [LinearOrder O] [Fintype A]
    (M : Matroid α) (d : α) (oldLabel : O → α) (movableLabel : A → α)
    {n : ℕ} (test : Fin n → α) (oldMark : O → Bool)
    (s : ℕ) (hs : Fintype.card A ≤ s)
    (hground : ∀ o, Sum.elim oldLabel movableLabel o ∈ M.E) :
    (freeMarkedPatterns M oldLabel movableLabel test oldMark).card ≤
      4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := by
  classical
  let eO := Fintype.orderIsoFinOfCardEq O rfl
  let eA := (Fintype.equivFin A).symm
  let e := Equiv.sumCongr eO.toEquiv eA
  let b : ℕ → α := fun k => if hk : k < Fintype.card O then oldLabel (eO ⟨k, hk⟩) else d
  let a : Fin (Fintype.card A) → α := movableLabel ∘ eA
  let m : Fin (Fintype.card O) → Bool := oldMark ∘ eO
  have hlabel : occurrenceLabel b a = Sum.elim oldLabel movableLabel ∘ e := by
    funext o
    cases o <;> simp [occurrenceLabel, b, a, e]
  have hsub : freeMarkedPatterns M oldLabel movableLabel test oldMark ⊆
      markedPivotPatterns M b a test m := by
    intro t ht
    obtain ⟨time, horder, htime, mark, hrecord⟩ := (Finset.mem_filter.mp ht).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, time ∘ e, ?_, htime.comp e.injective,
      mark ∘ eA, ?_⟩
    · intro i j hij
      exact horder (eO.strictMono hij)
    · intro f
      obtain ⟨o, hp, hm⟩ := hrecord f
      refine ⟨e.symm o, ?_, ?_⟩
      · rw [hlabel]
        exact (isPivot_reindex M (Sum.elim oldLabel movableLabel) time e (test f) (e.symm o)).2
          (by simpa using hp)
      · cases o <;> simpa [occurrenceMark, e, m, Function.comp_def] using hm
  apply (Finset.card_le_card hsub).trans
  apply card_markedPivotPatterns_le M b a test m s hs
  intro o
  rw [hlabel]
  exact hground (e o)

end MatroidProphet.Pivots

end OAI
