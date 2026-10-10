import OAI.NumberTheory.TwoPoint.Bounds.IntegerShiftWords
import OAI.NumberTheory.TwoPoint.Bounds.MatrixMomentNorm

namespace OAI

/-! Numerical words attached to the forced paths in the actual trace expansion. -/

namespace TwoPointCorrelations

open scoped Classical

variable {D V : Type*}

def integerStepWord (Q : Finset ℕ) (tuple : D → ℕ) {k : ℕ}
    (w : Fin k → D × (Q × Bool)) : List SignedStep :=
  (List.ofFn w).map (fun e => ⟨e.2.2, tuple e.1, e.2.1⟩)

lemma integerShiftEnd_site (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool)) :
    (shiftWordEnd (integerShiftNext Q tuple h) x w).2 =
      x.2 + wordDisplacement h (integerStepWord Q tuple w) := by
  induction k generalizing x with
  | zero => simp [shiftWordEnd, integerStepWord]
  | succ k ih =>
      rw [shiftWordEnd, ih]
      simp only [integerStepWord, List.ofFn_succ, List.map_cons, wordDisplacement_cons,
        integerShiftNext, Fin.tail_def]
      ring

lemma integer_closed_word_displacement (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ) {k : ℕ}
    (x : D × ℤ) (u v : Fin k → D × (Q × Bool))
    (he : shiftWordEnd (integerShiftNext Q tuple h) x u =
      shiftWordEnd (integerShiftNext Q tuple h) x v) :
    wordDisplacement h (integerStepWord Q tuple u ++ reverseWord (integerStepWord Q tuple v)) = 0 := by
  have hs := congrArg Prod.snd he
  rw [integerShiftEnd_site, integerShiftEnd_site] at hs
  rw [wordDisplacement_append, wordDisplacement_reverseWord]
  omega

lemma signedIntegerWeight_flip (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h : ℕ) (a : SignedStep) (n : ℤ) :
    signedIntegerWeight Q u eligible g center L K extra h a.flip (n + a.displacement h) =
      signedIntegerWeight Q u eligible g center L K extra h a n := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [signedIntegerWeight, SignedStep.flip, SignedStep.displacement]

/-- Periodicity permits using the departure center in both orientations.
All surviving cutoffs remain literal indicator conditions. -/
lemma signedIntegerWeight_departure (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h : ℕ) (a : SignedStep) (n : ℤ)
    (hperiod : ∀ q ∈ Q, ∀ z, center (z + (h * q * a.tuple : ℕ)) = center z) :
    signedIntegerWeight Q u eligible g center L K extra h a n =
      if a.padding ∈ Q ∧ eligible a.padding ∧ (a.padding : ℤ) ∣ n ∧
        integerEdgeKeep Q u eligible g L K extra n ∧
        integerEdgeKeep Q u eligible g L K extra (n + a.displacement h) then
        L * u a.padding * center n / (g n * g (n + a.displacement h)) else 0 := by
  classical
  rcases a with ⟨b, d, q⟩
  by_cases hq : q ∈ Q
  · cases b
    · have hd : (SignedStep.mk false d q).displacement h = -(h * q * d : ℕ) := by
        simp [SignedStep.displacement, Nat.cast_mul]
      have hn : n + -(h * q * d : ℕ) + (h * q * d : ℕ) = n := by ring
      have hc : center (n + -(h * q * d : ℕ)) = center n := by
        have hh := hperiod q hq (n + -(h * q * d : ℕ))
        rw [hn] at hh
        exact hh.symm
      have hqd : (q : ℤ) ∣ n + -(h * q * d : ℕ) ↔ (q : ℤ) ∣ n := by
        apply dvd_add_left
        apply dvd_neg.mpr
        exact_mod_cast dvd_mul_of_dvd_left (dvd_mul_left q h) d
      simp only [signedIntegerWeight, Bool.false_eq_true, ↓reduceIte, hd, directedIntegerEdge,
        hq, hn, true_and, hqd, hc]
      rw [mul_comm (g (n + -(h * q * d : ℕ))) (g n)]
      congr 1
      apply propext
      tauto
    · have hd : (SignedStep.mk true d q).displacement h = (h * q * d : ℕ) := by
        simp [SignedStep.displacement, Nat.cast_mul]
      simp [signedIntegerWeight, directedIntegerEdge, hd]
  · cases b <;> simp [signedIntegerWeight, directedIntegerEdge, hq]

variable [DecidableEq D]

lemma integerShiftWeight_nonzero (Q : Finset ℕ) (tuple : D → ℕ)
    (u : ℕ → ℝ) (eligible : D → ℕ → Prop) (g : ℤ → ℝ) (center : D → ℤ → ℝ)
    (L K : ℝ) (extra : D → ℤ → Prop) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (e : D × (Q × Bool)) (x : D × ℤ)
    (he : integerShiftWeight Q tuple u eligible g center L K extra h gate e x ≠ 0) :
    x.1 ≠ e.1 ∧ signedIntegerWeight Q u (eligible e.1) g (center e.1) L K (extra e.1) h
      ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 ≠ 0 := by
  unfold integerShiftWeight at he
  split_ifs at he with hc
  · exact ⟨hc.1, he⟩
  · contradiction

variable [Fintype V]

/-- Every nonzero half of the trace is nonbacktracking in its tuple labels.
The two halves can be joined without imposing a new condition at the joins. -/
theorem integerShiftWord_chain (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (u : ℕ → ℝ) (eligible : D → ℕ → Prop) (g : ℤ → ℝ) (center : D → ℤ → ℝ)
    (L K : ℝ) (extra : D → ℤ → Prop) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    {k : ℕ} (x : D × ℤ) (w : Fin k → D × (Q × Bool))
    (hw : shiftWordWeight embed (integerShiftNext Q tuple h)
      (integerShiftWeight Q tuple u eligible g center L K extra h gate) x w ≠ 0) :
    (x.1 :: (List.ofFn w).map Prod.fst).IsChain (fun a b => a ≠ b) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      have hp := mul_ne_zero_iff.mp hw
      have he := (retainedShiftWeight_nonzero _ _ _ _ _ hp.1).2
      have hc := (integerShiftWeight_nonzero Q tuple u eligible g center L K extra h gate
        (w 0) x he).1
      have ht := ih (integerShiftNext Q tuple h (w 0) x) (Fin.tail w) hp.2
      simp only [List.ofFn_succ, List.map_cons]
      exact ht.cons_cons hc

variable [Fintype D] [DecidableEq V]

omit [DecidableEq D] [Fintype V] [Fintype D] [DecidableEq V] in
lemma integerStateEmbedding_injective (site : V → ℤ) (hinj : Function.Injective site) :
    Function.Injective (fun x : D × V => (x.1, site x.2)) := by
  intro x y he
  exact Prod.ext (congrArg (fun z : D × ℤ => z.1) he)
    (hinj (congrArg (fun z : D × ℤ => z.2) he))

/-- The concrete nonbacktracking integer matrix has the forced-word moment
formula, with exactly one freely chosen starting site. -/
theorem integer_matrix_moment_forced_words
    (site : V → ℤ) (hinj : Function.Injective site) (Q : Finset ℕ) (tuple : D → ℕ)
    (u : ℕ → ℝ) (eligible : D → ℕ → Prop) (g : ℤ → ℝ) (center : D → ℤ → ℝ)
    (L K : ℝ) (extra : D → ℤ → Prop) (h : ℕ) (gate : D → ℤ → ℤ → Prop) (k : ℕ) :
    matrixFrobeniusSq (blockNonbacktrackingMatrix (fun d i j =>
      if gate d (site i) (site j) then
        integerEdgeMatrix site Q u (eligible d) g (center d) L K (extra d) h (tuple d) i j
      else 0) ^ k) =
      ∑ x : D × V, ∑ a : Fin k → D × (Q × Bool), ∑ b : Fin k → D × (Q × Bool),
        if shiftWordEnd (integerShiftNext Q tuple h) (x.1, site x.2) a =
          shiftWordEnd (integerShiftNext Q tuple h) (x.1, site x.2) b then
          shiftWordWeight (fun x : D × V => (x.1, site x.2)) (integerShiftNext Q tuple h)
            (integerShiftWeight Q tuple u eligible g center L K extra h gate) (x.1, site x.2) a *
          shiftWordWeight (fun x : D × V => (x.1, site x.2)) (integerShiftNext Q tuple h)
            (integerShiftWeight Q tuple u eligible g center L K extra h gate) (x.1, site x.2) b
        else 0 := by
  classical
  rw [block_integer_matrix_eq_shift]
  refine (shiftMatrix_moment_forced_words (fun x : D × V => (x.1, site x.2))
    (integerStateEmbedding_injective (D := D) site hinj) (integerShiftNext Q tuple h)
    (integerShiftWeight Q tuple u eligible g center L K extra h gate) k).trans ?_
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> rfl

end TwoPointCorrelations

end OAI
