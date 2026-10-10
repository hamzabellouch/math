import OAI.Analysis.LipschitzHilbert.Trees.UnaryRuns

namespace OAI

/-! Charge completed unary segments to themselves and remainders to the
next genuine interruption. The final path remainder is the only exception. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)

abbrev UnaryRunSegment := Σ r : R.runs, (P r).blocks

def unaryRunCharge (i : UnaryRunSegment R P) : Option (ℕ × ℕ) := by
  classical
  exact if i.2.val.2 < i.1.val.2 then some i.2.val else
    if i.1.val.2 < finish then some (i.1.val.2, i.1.val.2 + 1) else none

private theorem runSegment_eq (i j : UnaryRunSegment R P)
    (hr : i.1 = j.1) (hb : i.2.val.2 = j.2.val.2) : i = j := by
  rcases i with ⟨r, b⟩
  rcases j with ⟨s, c⟩
  dsimp only at hr hb
  subst s
  have hbc : b = c := (P r).end_injective hb
  subst c
  rfl

theorem unaryRunCharge_none (i : UnaryRunSegment R P)
    (hi : unaryRunCharge R P i = none) :
    i.2.val.2 = i.1.val.2 ∧ i.1.val.2 = finish := by
  have hb := (P i.1).bounds i.2.val i.2.property
  have hr := R.bounds i.1.val i.1.property
  unfold unaryRunCharge at hi
  split_ifs at hi with hseg hrun
  exact ⟨by omega, by omega⟩

theorem unaryRunCharge_some (i : UnaryRunSegment R P) (a b : ℕ)
    (hi : unaryRunCharge R P i = some (a,b)) :
    (a = i.2.val.1 ∧ b = i.2.val.2 ∧ i.2.val.2 < i.1.val.2) ∨
      (a = i.1.val.2 ∧ b = i.1.val.2 + 1 ∧
        i.2.val.2 = i.1.val.2 ∧ i.1.val.2 < finish) := by
  have hb := (P i.1).bounds i.2.val i.2.property
  unfold unaryRunCharge at hi
  split_ifs at hi with hseg hrun
  · have heq := Option.some.inj hi
    exact Or.inl ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm, hseg⟩
  · have heq := Option.some.inj hi
    exact Or.inr ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm,
      by omega, hrun⟩

theorem unaryRunCharge_none_unique (i j : UnaryRunSegment R P)
    (hi : unaryRunCharge R P i = none) (hj : unaryRunCharge R P j = none) : i = j := by
  obtain ⟨hbi, hri⟩ := unaryRunCharge_none R P i hi
  obtain ⟨hbj, hrj⟩ := unaryRunCharge_none R P j hj
  have hr : i.1 = j.1 := R.end_injective (hri.trans hrj.symm)
  exact runSegment_eq R P i j hr (by rw [hbi, hbj, hri, hrj])

theorem unaryRunCharge_bounds (i : UnaryRunSegment R P) (a b : ℕ)
    (hi : unaryRunCharge R P i = some (a,b)) :
    i.1.val.1 ≤ a ∧ b ≤ i.1.val.2 + 1 := by
  have hb := (P i.1).bounds i.2.val i.2.property
  rcases unaryRunCharge_some R P i a b hi with h | h
  · obtain ⟨rfl, rfl, _⟩ := h
    exact ⟨hb.1, by omega⟩
  · obtain ⟨rfl, rfl, _, _⟩ := h
    exact ⟨hb.1.trans (hb.2.1.le.trans hb.2.2), le_rfl⟩

theorem unaryRunCharge_disjoint (i j : UnaryRunSegment R P) (a b c d : ℕ)
    (hij : i ≠ j) (hi : unaryRunCharge R P i = some (a,b))
    (hj : unaryRunCharge R P j = some (c,d)) : b ≤ c ∨ d ≤ a := by
  by_cases hr : i.1 = j.1
  · have hne : i.2.val ≠ j.2.val := by
      intro heq
      exact hij (runSegment_eq R P i j hr (congrArg Prod.snd heq))
    have hjmem : j.2.val ∈ (P i.1).blocks := by
      rw [hr]
      exact j.2.property
    have horder := (P i.1).ordered i.2.val i.2.property j.2.val hjmem hne
    rcases unaryRunCharge_some R P i a b hi with hci | hci
    · rcases unaryRunCharge_some R P j c d hj with hcj | hcj
      · rcases hci with ⟨rfl, rfl, _⟩
        rcases hcj with ⟨rfl, rfl, _⟩
        exact horder
      · left
        rw [hci.2.1, hcj.1, ← hr]
        exact (P i.1).bounds i.2.val i.2.property |>.2.2
    · rcases unaryRunCharge_some R P j c d hj with hcj | hcj
      · right
        rw [hcj.2.1, hci.1, hr]
        exact (P j.1).bounds j.2.val j.2.property |>.2.2
      · have hend : i.2.val.2 = j.2.val.2 := by rw [hci.2.2.1, hcj.2.2.1, hr]
        exact False.elim (hij (runSegment_eq R P i j hr hend))
  · have hir := unaryRunCharge_bounds R P i a b hi
    have hjr := unaryRunCharge_bounds R P j c d hj
    have hne : i.1.val ≠ j.1.val := fun h => hr (Subtype.ext h)
    rcases R.separated i.1.property j.1.property hne with h | h
    · exact Or.inl (hir.2.trans ((Nat.succ_le_of_lt h).trans hjr.1))
    · exact Or.inr (hjr.2.trans ((Nat.succ_le_of_lt h).trans hir.1))

theorem unaryRunCharge_mass_drop (hn : Antitone n) {c : ℝ} (hc : c ≤ 1)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬ unary j → c ≤ n j - n (j + 1))
    (i : UnaryRunSegment R P) (a b : ℕ) (hi : unaryRunCharge R P i = some (a,b)) :
    n i.2.val.1 - 2 ≤ n a ∧ n a ≤ n i.2.val.1 ∧ c ≤ n a - n b := by
  have hb := (P i.1).bounds i.2.val i.2.property
  have hr := R.bounds i.1.val i.1.property
  rcases unaryRunCharge_some R P i a b hi with h | h
  · obtain ⟨rfl, rfl, hlast⟩ := h
    exact ⟨by linarith, le_rfl, hc.trans ((P i.1).completed i.2.val i.2.property hlast)⟩
  · obtain ⟨rfl, rfl, hend, hlast⟩ := h
    have hdrop := (P i.1).drop_lt_two i.2.val i.2.property
    rw [hend] at hdrop
    refine ⟨by linarith, hn (hb.2.1.le.trans hb.2.2), ?_⟩
    exact hinterruption i.1.val.2 (hr.1.trans hr.2.1.le) hlast
      (R.interruption i.1.val i.1.property hlast)

/-- All actual unary runs share one charged weight bound. Completed
segments pay their own drops, and every nonfinal remainder pays the next
interruption. There is only one uncharged final remainder on the path. -/
theorem unary_runs_weight_sum (hn : Antitone n) {c M μ : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12)
    (hmass : ∀ i : UnaryRunSegment R P, M ≤ n i.2.val.1)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬ unary j → c ≤ n j - n (j + 1)) :
    (∑ i : UnaryRunSegment R P, (n i.2.val.1) ^ ((-1 + μ) * (3 / 2 : ℝ))) ≤
      2 * (2 + 17 / c) * M ^ (-(1 / 2 : ℝ) + 3 * μ / 2) := by
  exact interval_charged_segment_weight_sum (fun i : UnaryRunSegment R P => n i.2.val.1)
    (unaryRunCharge R P) n hn (unaryRunCharge_none_unique R P)
    (unaryRunCharge_disjoint R P) hc hM hμ hmass
    (unaryRunCharge_mass_drop R P hn hc1 hinterruption)

omit R P in
/-- Construct the runs and their greedy segments directly from the unary
predicate and masses, then obtain the global negative-power weight bound. -/
theorem exists_unary_runs_weighted_partition (hn : Antitone n)
    (horder : start ≤ finish) {c M μ : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12)
    (hsmall : ∀ j, start ≤ j → j < finish → unary j → n j - n (j + 1) < 1)
    (hmass : ∀ j, start ≤ j → j < finish → unary j → M ≤ n j)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬ unary j → c ≤ n j - n (j + 1)) :
    ∃ R : UnaryRunPartition unary start finish,
      ∃ P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2,
        (∑ i : UnaryRunSegment R P, (n i.2.val.1) ^ ((-1 + μ) * (3 / 2 : ℝ))) ≤
          2 * (2 + 17 / c) * M ^ (-(1 / 2 : ℝ) + 3 * μ / 2) := by
  classical
  obtain ⟨R⟩ := exists_unary_run_partition unary start finish horder
  have hparts (r : R.runs) : Nonempty (UnarySegmentPartition n r.val.1 r.val.2) := by
    have hr := R.bounds r.val r.property
    apply exists_unary_segment_partition n r.val.1 r.val.2 hr.2.1.le
    intro j hj hjr
    exact hsmall j (hr.1.trans hj) (hjr.trans_le hr.2.2)
      (R.inside r.val r.property j hj hjr)
  let P := fun r : R.runs => Classical.choice (hparts r)
  refine ⟨R, P, unary_runs_weight_sum R P hn hc hc1 hM hμ ?_ hinterruption⟩
  intro i
  have hr := R.bounds i.1.val i.1.property
  have hb := (P i.1).bounds i.2.val i.2.property
  have hjr := hb.2.1.trans_le hb.2.2
  exact hmass i.2.val.1 (hr.1.trans hb.1) (hjr.trans_le hr.2.2)
    (R.inside i.1.val i.1.property i.2.val.1 hb.1 hjr)

end LipschitzHilbert

end

end OAI
