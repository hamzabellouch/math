import OAI.NumberTheory.TwoPoint.Bounds.ShiftedIntegerPaths
import OAI.NumberTheory.TwoPoint.Walks.ReversedSegments

namespace OAI

/-! The numerical support of a nonzero translated matrix path. -/

namespace TwoPointCorrelations

open scoped Classical

variable {D V : Type*} [DecidableEq D] [Fintype V]

lemma physicalShiftWeight_nonzero (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ)
    (e : D × (Q × Bool)) (x : D × ℤ)
    (he : physicalShiftWeight Q tuple h gate weight e x ≠ 0) :
    x.1 ≠ e.1 ∧ weight ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 ≠ 0 := by
  unfold physicalShiftWeight at he
  split_ifs at he with hc
  · exact ⟨hc.1, he⟩
  · contradiction

lemma physicalShiftWord_copy_chain (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool))
    (hw : shiftWordWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) x w ≠ 0) :
    (x.1 :: (List.ofFn w).map Prod.fst).IsChain (fun a b => a ≠ b) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      have hp := mul_ne_zero_iff.mp hw
      have he := (retainedShiftWeight_nonzero _ _ _ _ _ hp.1).2
      have hc := (physicalShiftWeight_nonzero Q tuple h gate weight (w 0) x he).1
      have ht := ih (integerShiftNext Q tuple h (w 0) x) (Fin.tail w) hp.2
      simp only [List.ofFn_succ, List.map_cons]
      exact ht.cons_cons hc

theorem physicalShiftWord_tuple_chain (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (hinj : Function.Injective tuple) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool))
    (hw : shiftWordWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) x w ≠ 0) :
    (integerStepWord Q tuple w).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  have hc := (physicalShiftWord_copy_chain embed Q tuple h gate weight x w hw).tail
  have hs := (List.isChain_map Prod.fst).mp hc
  apply (List.isChain_map (fun e : D × (Q × Bool) =>
    SignedStep.mk e.2.2 (tuple e.1) e.2.1.val)).mpr
  exact hs.imp (fun _ _ hne he => hne (hinj he))

theorem physicalShiftWord_pairs (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ) (pairs : Finset (ℕ × ℕ))
    (hsupport : ∀ t n, weight t n ≠ 0 → (t.tuple, t.padding) ∈ pairs)
    {k : ℕ} (x : D × ℤ) (w : Fin k → D × (Q × Bool))
    (hw : shiftWordWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) x w ≠ 0) :
    ∀ i, (tuple (w i).1, ((w i).2.1).val) ∈ pairs := by
  induction k generalizing x with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
      have hp := mul_ne_zero_iff.mp hw
      have he := (retainedShiftWeight_nonzero _ _ _ _ _ hp.1).2
      have hs := (physicalShiftWeight_nonzero Q tuple h gate weight (w 0) x he).2
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hsupport _ _ hs
      · exact ih (integerShiftNext Q tuple h (w 0) x) (Fin.tail w) hp.2 j

lemma scalarWalkProduct_one (h : ℕ) (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun _ _ => 1) n w = 1 := by
  induction w generalizing n with
  | nil => rfl
  | cons t w ih => simp only [scalarWalkProduct, ih, one_mul]

theorem integerPathMask_tuple_chain (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (hinj : Function.Injective tuple) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool))
    (hw : integerPathMask embed Q tuple h gate x w ≠ 0) :
    (integerStepWord Q tuple w).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  apply physicalShiftWord_tuple_chain embed Q tuple hinj h gate (fun _ _ => 1) x w
  rw [physicalShiftWord_product, scalarWalkProduct_one, mul_one]
  exact hw

end TwoPointCorrelations

end OAI
