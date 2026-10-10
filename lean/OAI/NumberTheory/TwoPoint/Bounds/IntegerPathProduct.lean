import OAI.NumberTheory.TwoPoint.Walks.ClosedPathProduct

namespace OAI

/-! Separate the copy, block, and endpoint gates from the signed arithmetic
edge product along an actual forced matrix path. -/

namespace TwoPointCorrelations

open scoped Classical

variable {D V : Type*}

noncomputable def integerStepMask (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (e : D × (Q × Bool)) (x : D × ℤ) : ℝ :=
  if x.1 ≠ e.1 ∧ gate e.1 x.2 (integerShiftNext Q tuple h e x).2 ∧
    integerShiftNext Q tuple h e x ∈ Set.range embed then 1 else 0

noncomputable def integerPathMask (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop) :
    {k : ℕ} → D × ℤ → (Fin k → D × (Q × Bool)) → ℝ
  | 0, _, _ => 1
  | _k + 1, x, w =>
      integerStepMask embed Q tuple h gate (w 0) x *
        integerPathMask embed Q tuple h gate (integerShiftNext Q tuple h (w 0) x) (Fin.tail w)

lemma integerPathMask_zero_or_one (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    {k : ℕ} (x : D × ℤ) (w : Fin k → D × (Q × Bool)) :
    integerPathMask embed Q tuple h gate x w = 0 ∨
      integerPathMask embed Q tuple h gate x w = 1 := by
  induction k generalizing x with
  | zero => exact Or.inr rfl
  | succ k ih =>
      simp only [integerPathMask, integerStepMask]
      split_ifs
      · simpa only [one_mul] using ih (integerShiftNext Q tuple h (w 0) x) (Fin.tail w)
      · exact Or.inl (zero_mul _)

variable [Fintype V] [DecidableEq D]

lemma retained_integerShiftWeight_eq_mask (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (u : ℕ → ℝ) (eligible : D → ℕ → Prop)
    (g : ℤ → ℝ) (center : D → ℤ → ℝ) (L K : ℝ) (extra : D → ℤ → Prop)
    (h : ℕ) (gate : D → ℤ → ℤ → Prop) (e : D × (Q × Bool)) (x : D × ℤ) :
    retainedShiftWeight embed (integerShiftNext Q tuple h)
      (integerShiftWeight Q tuple u eligible g center L K extra h gate) e x =
    integerStepMask embed Q tuple h gate e x *
      signedIntegerWeight Q u (eligible e.1) g (center e.1) L K (extra e.1) h
        ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 := by
  unfold integerStepMask
  by_cases hc : x.1 ≠ e.1
  · by_cases hg : gate e.1 x.2 (integerShiftNext Q tuple h e x).2
    · by_cases hr : integerShiftNext Q tuple h e x ∈ Set.range embed
      · simp [retainedShiftWeight, integerShiftWeight, hc, hg, hr]
      · simp [retainedShiftWeight, hc, hg, hr]
    · simp [retainedShiftWeight, integerShiftWeight, hc, hg]
  · simp [retainedShiftWeight, integerShiftWeight, hc]

theorem integerShiftWord_eq_mask_product (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (h : ℕ) (gate : D → ℤ → ℤ → Prop) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool)) :
    shiftWordWeight embed (integerShiftNext Q tuple h)
      (integerShiftWeight Q tuple u (fun d => eligible (tuple d)) g
        (fun d => center (tuple d)) L K (fun d => extra (tuple d)) h gate) x w =
      integerPathMask embed Q tuple h gate x w *
        scalarWalkProduct h (fun t => signedIntegerWeight Q u (eligible t.tuple) g
          (center t.tuple) L K (extra t.tuple) h t) x.2 (integerStepWord Q tuple w) := by
  induction k generalizing x with
  | zero => simp [shiftWordWeight, integerPathMask, integerStepWord, scalarWalkProduct]
  | succ k ih =>
      rw [shiftWordWeight, retained_integerShiftWeight_eq_mask, ih]
      simp only [integerPathMask, integerStepWord, List.ofFn_succ, List.map_cons, scalarWalkProduct]
      dsimp only [integerShiftNext, Fin.tail_def]
      ring

theorem integerShiftWord_pair_product (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (h : ℕ) (gate : D → ℤ → ℤ → Prop) {k : ℕ}
    (x : D × ℤ) (a b : Fin k → D × (Q × Bool))
    (hend : shiftWordEnd (integerShiftNext Q tuple h) x a =
      shiftWordEnd (integerShiftNext Q tuple h) x b) :
    shiftWordWeight embed (integerShiftNext Q tuple h)
      (integerShiftWeight Q tuple u (fun d => eligible (tuple d)) g
        (fun d => center (tuple d)) L K (fun d => extra (tuple d)) h gate) x a *
      shiftWordWeight embed (integerShiftNext Q tuple h)
      (integerShiftWeight Q tuple u (fun d => eligible (tuple d)) g
        (fun d => center (tuple d)) L K (fun d => extra (tuple d)) h gate) x b =
      (integerPathMask embed Q tuple h gate x a * integerPathMask embed Q tuple h gate x b) *
        scalarWalkProduct h (fun t => signedIntegerWeight Q u (eligible t.tuple) g
          (center t.tuple) L K (extra t.tuple) h t) x.2
          (integerStepWord Q tuple a ++ reverseWord (integerStepWord Q tuple b)) := by
  have he := congrArg (fun y : D × ℤ => y.2) hend
  rw [integerShiftEnd_site, integerShiftEnd_site] at he
  have hd : wordDisplacement h (integerStepWord Q tuple a) =
      wordDisplacement h (integerStepWord Q tuple b) := by omega
  rw [integerShiftWord_eq_mask_product, integerShiftWord_eq_mask_product]
  rw [← signedIntegerWeight_closed_pair Q u eligible g center L K extra h x.2 _ _ hd]
  ring

end TwoPointCorrelations

end OAI
