import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet.ExitContract

open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reverseCost_nonneg (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hf : ∀ k S S', 0 ≤ f k S S')
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    0 ≤ reverseCost M hE κ D G n f m k S C := by
  induction m generalizing k S with
  | zero => exact le_rfl
  | succ m ih => exact add_nonneg (hf _ _ _) (ih _ _)

lemma transition_cost_le_total (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hf : ∀ k S S', 0 ≤ f k S S')
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (t : ReverseTransition α) (ht : t ∈ reverseTrace M hE κ D G n m k S C) :
    f t.time t.before t.after ≤ reverseCost M hE κ D G n f m k S C := by
  induction m generalizing k S with
  | zero => simp [reverseTrace] at ht
  | succ m ih =>
    simp only [reverseTrace, List.mem_cons] at ht
    rw [reverseCost]
    rcases ht with rfl | ht
    · exact le_add_of_nonneg_right (reverseCost_nonneg M hE κ D G n f hf _ _ _ _)
    · exact (ih _ _ ht).trans (le_add_of_nonneg_left (hf _ _ _))

/-- A finite run starting live and ending absent contains an actual exit step. -/
lemma exists_exit_transition (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) (d : α) (h : ℕ)
    (hin : d ∈ S h)
    (hout : d ∉ reverseFinal M hE κ D G n m k S C h) :
    ∃ t ∈ reverseTrace M hE κ D G n m k S C, d ∈ t.before h ∧ d ∉ t.after h := by
  induction m generalizing k S with
  | zero => exact (hout hin).elim
  | succ m ih =>
    let S' := (reverseStepTree M hE κ k D S G n).run C
    by_cases hs : d ∈ S' h
    · obtain ⟨t, ht, htin, htout⟩ := ih (k-1) S' hs hout
      exact ⟨t, List.mem_cons_of_mem _ ht, htin, htout⟩
    · exact ⟨⟨k, S, S'⟩, List.mem_cons_self, hin, hs⟩

/-- Every nonloop has an actual exit, for every realization of the original mask. -/
theorem nonloop_exits (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) (C : Finset α) :
    ∃ t ∈ reverseTrace M hE κ D G h (pathHorizon h + 1) (-1)
        (fun _ => Set.univ) C, d ∈ t.before h ∧ d ∉ t.after h := by
  apply exists_exit_transition M hE κ D G h (pathHorizon h + 1) (-1)
    (fun _ => Set.univ) C d h (Set.mem_univ d)
  rw [reverseFinal_from_univ M hE κ D G h hG h le_rfl C]
  exact hd

/-- Probability of an actual low-hazard exit in a finite reverse run. -/
theorem low_exit_event_lt_half (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    bitsExpectation q univ (fun C =>
      if ∃ t ∈ reverseTrace M hE κ D G n m k S C,
        d ∈ t.before h ∧ d ∉ t.after h ∧
          reverseHazard M hE κ D G q d h t.time t.before < exitThreshold
      then (1 : ℝ) else 0) < 1 / 2 := by
  let f := bandExitCost M hE κ D G q d h 0 exitThreshold
  have hf (l : ℤ) (R R' : ℕ → Set α) : 0 ≤ f l R R' := by
    dsimp [f, bandExitCost]
    split_ifs <;> norm_num
  have hevent : bitsExpectation q univ (fun C =>
      if ∃ t ∈ reverseTrace M hE κ D G n m k S C,
        d ∈ t.before h ∧ d ∉ t.after h ∧
          reverseHazard M hE κ D G q d h t.time t.before < exitThreshold
      then (1 : ℝ) else 0) ≤ reverseMeanCost M hE κ D G n q f m k S := by
    apply bitsExpectation_mono q hq0 hq1
    intro C hC
    split_ifs with he
    · obtain ⟨t, ht, hin, hout, hp⟩ := he
      have ht' := transition_cost_le_total M hE κ D G n f hf m k S C t ht
      have hp0 := reverseHazard_nonneg M hE κ D G q hq0 hq1 d h t.time t.before
      simpa [f, bandExitCost, hp0, hp, hin, hout] using ht'
    · exact reverseCost_nonneg M hE κ D G n f hf m k S C
  have hcost : reverseMeanCost M hE κ D G n q f m k S =
      reverseMeanCost M hE κ D G n q
        (lowHazardCost M hE κ D G q d h exitThreshold) m k S := by
    rw [← bandHazardCost_mean_eq_exit M hE κ D G n hG q hq0 hq1 d h hh 0 exitThreshold m k S closed]
    congr 1
    funext l R R'
    have hp0 := reverseHazard_nonneg M hE κ D G q hq0 hq1 d h l R
    simp only [bandHazardCost, lowHazardCost, hp0, true_and]
    simp only [and_comm]
  rw [hcost] at hevent
  exact hevent.trans_lt
    (reverse_low_hazard_lt_half M hE κ D G n hG q hq0 hq1 d h hh m k S closed)

/-- All three conclusions of manuscript `lem:exit`, on actual nominal paths.
The natural reverse index `i` denotes manuscript time `b = -i`; its range
is precisely `activation h ≤ b ≤ 0`. -/
theorem exit_mass (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) :
    (∀ C : Finset α,
      d ∉ reverseFinal M hE κ D G h (pathHorizon h + 1) (-1)
        (fun _ => Set.univ) C h) ∧
    bitsExpectation q univ (fun C =>
      if ∃ t ∈ reverseTrace M hE κ D G h (pathHorizon h + 1) (-1)
          (fun _ => Set.univ) C,
        d ∈ t.before h ∧ d ∉ t.after h ∧
          reverseHazard M hE κ D G q d h t.time t.before < exitThreshold
      then (1 : ℝ) else 0) < 1 / 2 ∧
    exitThreshold / 2 ≤ ∑ i ∈ range (pathHorizon h + 1),
      bitsExpectation q univ (pathExitSquare M hE κ D G q d h i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C
    rw [reverseFinal_from_univ M hE κ D G h hG h le_rfl C]
    exact hd
  · convert low_exit_event_lt_half M hE κ D G h hG q hq0 hq1 d h le_rfl
      (pathHorizon h + 1) (-1) (fun _ => Set.univ) (reverseClosed_univ M hE κ D (-1)) using 1
    congr 2
    funext C
    split_ifs <;> rfl
  · exact path_squared_exit_mass M hE κ D G hG q hq0 hq1 d hd h

/-- Source-facing form with existence of the actual exit transition explicit.
The final absence clause in `exit_mass` is strengthened to a witness in the
single-mask reverse trace; the probability and square-sum clauses are unchanged. -/
theorem exit_mass_actual (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) :
    (∀ C : Finset α,
      ∃ t ∈ reverseTrace M hE κ D G h (pathHorizon h + 1) (-1)
          (fun _ => Set.univ) C, d ∈ t.before h ∧ d ∉ t.after h) ∧
    bitsExpectation q univ (fun C =>
      if ∃ t ∈ reverseTrace M hE κ D G h (pathHorizon h + 1) (-1)
          (fun _ => Set.univ) C,
        d ∈ t.before h ∧ d ∉ t.after h ∧
          reverseHazard M hE κ D G q d h t.time t.before < exitThreshold
      then (1 : ℝ) else 0) < 1 / 2 ∧
    exitThreshold / 2 ≤ ∑ i ∈ range (pathHorizon h + 1),
      bitsExpectation q univ (pathExitSquare M hE κ D G q d h i) := by
  exact ⟨nonloop_exits M hE κ D G hG d hd h,
    (exit_mass M hE κ D G hG q hq0 hq1 d hd h).2⟩

end MatroidProphet.ExitContract

end OAI
