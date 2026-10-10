import OAI.NumberTheory.TwoPoint.Bounds.IntegerVertexMask

namespace OAI

/-! Arithmetic translation leaves the physical copy and block gates fixed. -/

namespace TwoPointCorrelations

open scoped Classical

variable {D V : Type*}

lemma scalarWalkProduct_translate (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (c n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun t z => weight t (z + c)) n w =
      scalarWalkProduct h weight (n + c) w := by
  induction w generalizing n with
  | nil => rfl
  | cons t w ih =>
      simp only [scalarWalkProduct, ih]
      rw [show n + t.displacement h + c = n + c + t.displacement h by ring]

noncomputable def physicalShiftWeight (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ)
    (e : D × (Q × Bool)) (x : D × ℤ) : ℝ :=
  if x.1 ≠ e.1 ∧ gate e.1 x.2 (integerShiftNext Q tuple h e x).2 then
    weight ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 else 0

variable [Fintype V] [DecidableEq D]

lemma retained_physicalShiftWeight (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ) (e : D × (Q × Bool)) (x : D × ℤ) :
    retainedShiftWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) e x =
      integerStepMask embed Q tuple h gate e x *
        weight ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 := by
  by_cases hc : x.1 ≠ e.1
  · by_cases hg : gate e.1 x.2 (integerShiftNext Q tuple h e x).2
    · by_cases hr : integerShiftNext Q tuple h e x ∈ Set.range embed
      · simp [retainedShiftWeight, physicalShiftWeight, integerStepMask, hc, hg, hr]
      · simp [retainedShiftWeight, integerStepMask, hr]
    · simp [retainedShiftWeight, physicalShiftWeight, integerStepMask, hc, hg]
  · simp [retainedShiftWeight, physicalShiftWeight, integerStepMask, hc]

theorem physicalShiftWord_product (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool)) :
    shiftWordWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) x w =
      integerPathMask embed Q tuple h gate x w *
        scalarWalkProduct h weight x.2 (integerStepWord Q tuple w) := by
  induction k generalizing x with
  | zero => simp [shiftWordWeight, integerPathMask, integerStepWord, scalarWalkProduct]
  | succ k ih =>
      rw [shiftWordWeight, retained_physicalShiftWeight, ih]
      simp only [integerPathMask, integerStepWord, List.ofFn_succ, List.map_cons, scalarWalkProduct]
      dsimp only [integerShiftNext, Fin.tail_def]
      ring

theorem physicalShiftWord_closed_pair (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    (c : ℤ) {k : ℕ} (x : D × ℤ) (a b : Fin k → D × (Q × Bool))
    (hend : shiftWordEnd (integerShiftNext Q tuple h) x a =
      shiftWordEnd (integerShiftNext Q tuple h) x b) :
    shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + c))) x a *
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + c))) x b =
      (integerPathMask embed Q tuple h gate x a * integerPathMask embed Q tuple h gate x b) *
        scalarWalkProduct h weight (x.2 + c) (integerClosedWordCode Q tuple (a, b)) := by
  have he := congrArg (fun y : D × ℤ => y.2) hend
  rw [integerShiftEnd_site, integerShiftEnd_site] at he
  have hd : wordDisplacement h (integerStepWord Q tuple a) =
      wordDisplacement h (integerStepWord Q tuple b) := by omega
  rw [physicalShiftWord_product, physicalShiftWord_product,
    scalarWalkProduct_translate, scalarWalkProduct_translate]
  unfold integerClosedWordCode
  rw [← scalarWalkProduct_closed_pair h weight hflip (x.2 + c) _ _ hd]
  ring

noncomputable def maskedSignedIntegerWeight (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ) (keep : ℤ → Prop)
    (t : SignedStep) (n : ℤ) : ℝ :=
  vertexIndicator keep n *
    signedIntegerWeight Q u (eligible t.tuple) g (center t.tuple) L K
      (extra t.tuple) h t n * vertexIndicator keep (n + t.displacement h)

lemma maskedSignedIntegerWeight_flip (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ) (keep : ℤ → Prop)
    (t : SignedStep) (n : ℤ) :
    maskedSignedIntegerWeight Q u eligible g center L K extra h keep
      t.flip (n + t.displacement h) =
      maskedSignedIntegerWeight Q u eligible g center L K extra h keep t n := by
  unfold maskedSignedIntegerWeight
  rw [signedIntegerWeight_flip, SignedStep.displacement_flip]
  rw [show n + t.displacement h + -t.displacement h = n by ring]
  dsimp only [SignedStep.flip]
  ring

theorem physicalShiftWeight_masked_eq_integer (Q : Finset ℕ) (tuple : D → ℕ)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (center : ℕ → ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (h : ℕ) (gate : D → ℤ → ℤ → Prop) (keep : ℤ → Prop) :
    physicalShiftWeight Q tuple h gate
      (maskedSignedIntegerWeight Q u eligible g center L K extra h keep) =
      integerShiftWeight Q tuple u (fun d => eligible (tuple d)) g
        (fun d => center (tuple d)) L K (fun d => extra (tuple d)) h
        (integerVertexGate gate keep) := by
  funext e x
  by_cases hc : x.1 ≠ e.1 <;>
    by_cases hg : gate e.1 x.2 (integerShiftNext Q tuple h e x).2 <;>
    by_cases hn : keep x.2 <;>
    by_cases hm : keep (integerShiftNext Q tuple h e x).2 <;>
    simp_all [physicalShiftWeight, maskedSignedIntegerWeight, integerShiftWeight,
      integerVertexGate, vertexIndicator, integerShiftNext]

end TwoPointCorrelations

end OAI
