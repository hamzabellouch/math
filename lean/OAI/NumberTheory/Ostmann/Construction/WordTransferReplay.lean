import OAI.NumberTheory.Ostmann.Construction.WordTransferTemplate

namespace OAI

namespace Ostmann

open scoped Classical

/-- At a leaf, the state contains the original word whose Fourier factor
is evaluated. Internal states are never queried by the leaf list. -/
noncomputable def wordTransferLeafValue {σ : Type*} : WordTransferState σ → ℕ
  | ⟨0, .leaf word, x⟩ => (word.map x).prod
  | ⟨_ + 1, _, _⟩ => 1

noncomputable def wordTransferSignedLeaf {σ : Type*}
    (z : (WordTransferState σ × ℤ) × Bool) : Bool × ℤ :=
  (z.2, (wordTransferLeafValue z.1.1 : ℤ))

theorem WordTransferTemplate.branching_valid {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (template.branching t hn).Valid (fun i => (x i : ℤ)) := by
  induction template generalizing x with
  | leaf word => trivial
  | @node n d l r hl hr =>
    obtain ⟨P, hp, hvL, hvR⟩ := hv
    have hs := wordTransferStep_valid d l r x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P hp
    have he := wordTransferStep_apply d l r x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P hp
    change _ ∧ _ ∧ _
    refine ⟨hs, ?_, ?_⟩
    · rw [he]
      exact hl _ _ hn.2.1 hvL
    · rw [he]
      exact hr _ _ hn.2.2 hvR

theorem wordTransferSignedLeaf_flip {σ : Type*}
    (l : List ((WordTransferState σ × ℤ) × Bool)) :
    ((l.map (fun z => (z.1, !z.2))).map wordTransferSignedLeaf) =
      (l.map wordTransferSignedLeaf).map BranchingWordHistory.flipSigned := by
  simp only [List.map_map]
  rfl

theorem WordTransferTemplate.branching_leaves {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (template.branching t hn).integerLeaves (fun i => (x i : ℤ)) =
      (transferLeafList (wordTransferSystem σ) n (template.state x) t).map wordTransferSignedLeaf := by
  induction template generalizing x with
  | leaf word =>
    simp only [WordTransferTemplate.branching, BranchingWordHistory.integerLeaves,
      WordTransferTemplate.state, transferLeafList, List.map_cons, List.map_nil,
      wordTransferSignedLeaf, wordTransferLeafValue]
    congr 2
    clear hv
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  | @node n d l r hl hr =>
    obtain ⟨P, hp, hvL, hvR⟩ := hv
    have he := wordTransferStep_apply d l r x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P hp
    simp only [WordTransferTemplate.branching, BranchingWordHistory.integerLeaves, transferLeafList]
    rw [hp.historyPivot_eq, he]
    rw [List.map_append, wordTransferSignedLeaf_flip]
    rw [hl _ _ hn.2.1 hvL, hr _ _ hn.2.2 hvR]
    rfl

/-- Thus the actual arithmetic history has the explicitly constructed
polynomial divisibility gates needed by the one-sided estimate. -/
theorem WordTransferTemplate.polynomial_gates {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    ∀ F ∈ (template.branching t hn).pivotFormulas .prime,
      F.cleared.denominator ∣ MvPolynomial.eval₂Hom (RingHom.id ℤ)
        (fun i => (x i : ℤ)) F.cleared.numerator :=
  (BranchingWordHistory.branching_integer_polynomial_tests _ _).mp
    (template.branching_valid x t hn hv)

end Ostmann

end OAI
