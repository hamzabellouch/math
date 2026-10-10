import OAI.NumberTheory.Ostmann.Construction.WordTransferGuard

namespace OAI

/-! # All branching support tests are the original recursive arithmetic support -/

namespace Ostmann

open scoped Classical

noncomputable def WordTransferTemplate.guards {σ : Type*} :
    {n : ℕ} → WordTransferTemplate σ n → (t : FrequencyTree ℤ n) →
      NonzeroInternalFrequencies n t → (σ → HistoryFormula σ) → List (WordTransferGuard σ)
  | 0, .leaf _, _, _, _ => []
  | n + 1, .node d l r, t, hn, env =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
      wordTransferGuard d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1 env ::
        (l.guards t.2.1 hn.2.1 (BranchingWordHistory.updatedFormulas step env) ++
          r.guards t.2.2 hn.2.2 (BranchingWordHistory.updatedFormulas step env))

theorem wordTransferUpdatedFormulas_nat {σ : Type*} {n : ℕ}
    (d : WordTransferNode σ) (l r : WordTransferTemplate σ n) (x : σ → ℕ)
    (s v w : ℤ) (hs : s ≠ 0) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P)
    (env : σ → HistoryFormula σ) (a : σ → ℤ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    ∀ i, (BranchingWordHistory.updatedFormulas (wordTransferStep d s v w hs) env i).value
      (fun j => (a j : ℚ)) = (Function.update x d.target P i : ℚ) := by
  have hu := BranchingWordHistory.updatedFormulas_value (wordTransferStep d s v w hs)
    env (fun j => (a j : ℚ)) (fun i => (x i : ℤ))
    (by intro i; simpa only [Int.cast_natCast] using henv i)
    (wordTransferStep_valid d l r x s v w P hp)
  rw [wordTransferStep_apply d l r x s v w P hp] at hu
  intro i
  simpa only [Int.cast_natCast] using hu i

/-- The list contains precisely the original support conditions at every
node, including the independent substitutions on the two child branches. -/
theorem WordTransferTemplate.guards_iff {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ)
    (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (∀ g ∈ template.guards t hn env, g.ValidAt a) ↔
      ValidTransferHistory (wordTransferSystem σ) n (template.state x) t := by
  induction template generalizing env x with
  | leaf word => simp [guards, ValidTransferHistory]
  | @node n d l r hl hr =>
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
    change (∀ g ∈ wordTransferGuard d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1 env ::
      (l.guards t.2.1 hn.2.1 (BranchingWordHistory.updatedFormulas step env) ++
        r.guards t.2.2 hn.2.2 (BranchingWordHistory.updatedFormulas step env)), g.ValidAt a) ↔ _
    simp only [List.mem_cons, List.mem_append, or_imp, forall_and, forall_eq]
    rw [wordTransferGuard_iff d l r _ _ _ hn.1 env a x henv]
    constructor
    · rintro ⟨⟨P, hp⟩, hL, hR⟩
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ hn.1 P hp env a henv
      exact ⟨P, hp, (hl _ _ _ _ hu).mp hL, (hr _ _ _ _ hu).mp hR⟩
    · rintro ⟨P, hp, hL, hR⟩
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ hn.1 P hp env a henv
      exact ⟨⟨P, hp⟩, (hl _ _ _ _ hu).mpr hL, (hr _ _ _ _ hu).mpr hR⟩

theorem WordTransferTemplate.guards_length {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (template.guards t hn env).length = 2 ^ n - 1 := by
  induction template generalizing env with
  | leaf word => rfl
  | @node n d l r hl hr =>
    simp only [guards, List.length_cons, List.length_append, hl, hr, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem WordTransferTemplate.guards_pivots {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (template.guards t hn env).map WordTransferGuard.pivot =
      (template.branching t hn).pivotFormulas env := by
  induction template generalizing env with
  | leaf word => rfl
  | @node n d l r hl hr =>
    simp only [guards, branching, BranchingWordHistory.pivotFormulas,
      List.map_cons, List.map_append, hl, hr]
    rfl

end Ostmann

end OAI
