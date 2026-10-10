import OAI.Probability.MatroidSecretary.Pivots.MarkedPivotSpecification
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# Complete finite occurrence version of the marked-pivot lemma

The counting proof is inherited from the actual greedy-support/affine-sign
argument. We bridge finite old lists to it only in the nonempty ambient case;
the empty ambient case is proved directly, not excluded by an inhabitedness
premise. Existence and uniqueness ensure the counted family does not omit an
interleaving merely because its record predicate has no witness.
-/

namespace MatroidProphet.MarkedPivots

open scoped BigOperators

variable {α : Type*} [Fintype α] {r q n : ℕ}

omit [Fintype α] in
lemma records_unique (M : Matroid α) (old : Fin r → α) (movable : Fin q → α)
    (test : Fin n → α) (time : Occurrences r q → ℕ)
    (htime : Function.Injective time) (oldMark : Fin r → Bool)
    (movableMark : Fin q → Bool) {a b : Finset (Fin n)}
    (ha : Records M old movable test time oldMark movableMark a)
    (hb : Records M old movable test time oldMark movableMark b) : a = b := by
  apply Finset.ext
  intro f
  obtain ⟨o, ho, hma⟩ := ha f
  obtain ⟨p, hp, hmb⟩ := hb f
  have hop : o = p := Pivots.pivot_unique M (label old movable) time htime ho hp
  subst p
  exact hma.symm.trans hmb

lemma records_existsUnique (M : Matroid α) (old : Fin r → α) (movable : Fin q → α)
    (test : Fin n → α) (time : Occurrences r q → ℕ)
    (htime : Function.Injective time) (oldMark : Fin r → Bool)
    (movableMark : Fin q → Bool) (hspan : M.closure (Set.range old) = M.E)
    (htest : ∀ f, test f ∈ M.E ∧ test f ∉ M.closure ∅) :
    ∃! pattern, Records M old movable test time oldMark movableMark pattern := by
  have hspan' : ∀ f, test f ∈ M.closure (Set.range (label old movable)) := by
    intro f
    apply M.closure_subset_closure ?_ (hspan.symm ▸ (htest f).1)
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩
  obtain ⟨pattern, hp⟩ := Pivots.recordsPivots_exists M (label old movable)
    test time oldMark movableMark (fun f => (htest f).2) hspan'
  refine ⟨pattern, hp, ?_⟩
  intro other ho
  exact records_unique M old movable test time htime oldMark movableMark ho hp

lemma card_patterns_le (M : Matroid α) (old : Fin r → α) (movable : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool) (s : ℕ) (hqs : q ≤ s)
    (hold : ∀ i, old i ∈ M.E) (hmovable : ∀ i, movable i ∈ M.E) :
    (patterns M old movable test oldMark).card ≤
      4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := by
  classical
  by_cases hα : Nonempty α
  · let b : ℕ → α := fun i => if hi : i < r then old ⟨i, hi⟩ else Classical.choice hα
    have hb : ∀ i : Fin r, b i.val = old i := by
      intro i
      simp [b, i.isLt]
    have hl : Pivots.occurrenceLabel (r := r) b movable = label old movable := by
      funext o
      cases o with
      | inl i => exact hb i
      | inr i => rfl
    have hf : Pivots.markedPivotPatterns M b movable test oldMark =
        patterns M old movable test oldMark := by
      unfold Pivots.markedPivotPatterns patterns
      simp only [hl]
      rfl
    rw [← hf]
    apply Pivots.card_markedPivotPatterns_le M b movable test oldMark s hqs
    intro o
    rw [hl]
    cases o with
    | inl i => exact hold i
    | inr i => exact hmovable i
  · have hn : n = 0 := by
      by_contra hn
      exact hα ⟨test ⟨0, Nat.pos_of_ne_zero hn⟩⟩
    subst n
    have hc : (patterns M old movable test oldMark).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a _ b _
      exact Subsingleton.elim a b
    have hs : 1 ≤ ∑ k ∈ Finset.Iic s, (0 : ℕ).choose k := by
      simpa using (Finset.single_le_sum (fun k (_ : k ∈ Finset.Iic s) =>
        Nat.zero_le ((0 : ℕ).choose k)) (show 0 ∈ Finset.Iic s by simp))
    have hp : 1 ≤ 4 ^ s := Nat.one_le_pow s 4 (by decide)
    exact hc.trans (by nlinarith)

/-- The complete source-level marked-pivot contract. -/
theorem sourceContract : SourceContract := by
  intro α _ M r q n s old movable test oldMark hqs hold hmovable hspan _ htest
  refine ⟨card_patterns_le M old movable test oldMark s hqs hold hmovable, ?_⟩
  intro time _ htime movableMark
  exact records_existsUnique M old movable test time htime oldMark movableMark hspan htest

end MatroidProphet.MarkedPivots

end OAI
