import OAI.Combinatorics.BalancedRyser.Probability.OverlapOrdering
import OAI.Combinatorics.BalancedRyser.Probability.PatternMoments

namespace OAI

namespace Balanced.PatternMoments

open scoped BigOperators

variable {A γ : Type*}

theorem scheduleAllowed_ofFn_of_precedes (rel : A → A → Prop) :
    ∀ {n : ℕ} (σ : Fin n → Bool) (x : Fin n → A) (pre : List A),
      (∀ i, σ i = true ∨ (∃ b ∈ pre, rel b (x i)) ∨
        ∃ j, j < i ∧ rel (x j) (x i)) →
      scheduleAllowed (fun pre a => ∃ b ∈ pre, rel b a)
        (List.ofFn σ) (List.ofFn x) pre := by
  intro n
  induction n with
  | zero =>
      intro σ x pre h
      simp [scheduleAllowed]
  | succ n ih =>
      intro σ x pre h
      rw [List.ofFn_succ, List.ofFn_succ]
      constructor
      · rcases h 0 with hroot | hpre | ⟨j, hj, hrel⟩
        · exact Or.inl hroot
        · exact Or.inr hpre
        · exact (Fin.not_lt_zero j hj).elim
      · apply ih (fun i => σ i.succ) (fun i => x i.succ) (x 0 :: pre)
        intro i
        rcases h i.succ with hroot | hpre | ⟨j, hj, hrel⟩
        · exact Or.inl hroot
        · exact Or.inr (Or.inl ⟨hpre.choose, List.mem_cons_of_mem _ hpre.choose_spec.1,
            hpre.choose_spec.2⟩)
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · exact Or.inr (Or.inl ⟨x 0, List.mem_cons_self, hrel⟩)
          · exact Or.inr (Or.inr ⟨j, Fin.succ_lt_succ_iff.mp hj, hrel⟩)

theorem rootCount_ofFn {n : ℕ} (σ : Fin n → Bool) :
    rootCount (List.ofFn σ) = ∑ i, if σ i then 1 else 0 := by
  induction n with
  | zero => simp [rootCount]
  | succ n ih =>
      simp only [List.ofFn_succ, rootCount, Fin.sum_univ_succ]
      rw [ih]

theorem rootCount_ofFn_mem {n : ℕ} (R : Finset (Fin n)) :
    rootCount (List.ofFn (fun i => decide (i ∈ R))) = R.card := by
  rw [rootCount_ofFn]
  simp

variable [DecidableEq γ]

def supportOverlap (C : A → Finset γ) (K₀ : Finset γ)
    (pre : List A) (a : A) : Prop :=
  ¬ Disjoint (C a \ K₀) (pre.foldr (fun b U => U ∪ (C b \ K₀)) ∅)

lemma supportOverlap_iff (C : A → Finset γ) (K₀ : Finset γ)
    (pre : List A) (a : A) :
    supportOverlap C K₀ pre a ↔
      ∃ b ∈ pre, ((C b \ K₀) ∩ (C a \ K₀)).Nonempty := by
  classical
  induction pre with
  | nil => simp [supportOverlap]
  | cons b pre ih =>
      simp only [supportOverlap, List.foldr_cons, Finset.disjoint_union_right,
        not_and_or] at ih ⊢
      rw [ih]
      simp [Finset.not_disjoint_iff_nonempty_inter, Finset.inter_comm, or_comm]

theorem exists_support_schedule {s : ℕ} (C : A → Finset γ) (K₀ : Finset γ)
    (a : Fin (2 * s) → A)
    (hnoiso : ∀ i, ∃ j, j ≠ i ∧ ((C (a j) \ K₀) ∩ (C (a i) \ K₀)).Nonempty) :
    ∃ π : Equiv.Perm (Fin (2 * s)), ∃ σ : Fin (2 * s) → Bool,
      rootCount (List.ofFn σ) ≤ s ∧
      scheduleAllowed (supportOverlap C K₀) (List.ofFn σ)
        (List.ofFn (fun i => a (π i))) [] := by
  classical
  obtain ⟨π, R, hcard, hprev⟩ :=
    OverlapOrdering.exists_pattern_ordering (fun i => C (a i)) K₀ hnoiso
  refine ⟨π, fun i => decide (i ∈ R), ?_, ?_⟩
  · simpa only [rootCount_ofFn_mem] using hcard
  · have hoverlap : supportOverlap C K₀ =
        (fun pre b => ∃ c ∈ pre, ((C c \ K₀) ∩ (C b \ K₀)).Nonempty) := by
      funext pre b
      exact propext (supportOverlap_iff C K₀ pre b)
    rw [hoverlap]
    apply scheduleAllowed_ofFn_of_precedes
    intro i
    by_cases hi : i ∈ R
    · exact Or.inl (by simp [hi])
    · exact Or.inr (Or.inr (hprev i hi))

end Balanced.PatternMoments

end OAI
