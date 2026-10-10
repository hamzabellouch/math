import OAI.NumberTheory.TwoPoint.Bounds.ShiftMatrixWords
import OAI.NumberTheory.TwoPoint.Bounds.IntegerEdges
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords

namespace OAI

/-! The actual centered integer-edge matrix as a matrix of forced signed shifts. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def signedIntegerWeight (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h : ℕ) (a : SignedStep) (n : ℤ) : ℝ :=
  if a.forward then
    directedIntegerEdge Q u eligible g center L K extra h a.tuple a.padding n
      (n + a.displacement h)
  else
    directedIntegerEdge Q u eligible g center L K extra h a.tuple a.padding
      (n + a.displacement h) n

lemma forward_edge_as_shift (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d q : ℕ) (n m : ℤ) :
    directedIntegerEdge Q u eligible g center L K extra h d q n m =
      if m = n + (SignedStep.mk true d q).displacement h then
        signedIntegerWeight Q u eligible g center L K extra h ⟨true, d, q⟩ n else 0 := by
  classical
  have hd : (SignedStep.mk true d q).displacement h = (h * q * d : ℕ) := by
    simp [SignedStep.displacement, Nat.cast_mul]
  rw [hd]
  by_cases he : m = n + (h * q * d : ℕ)
  · subst m
    simp only [signedIntegerWeight, ↓reduceIte, hd]
  · have hf : ¬(q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ n ∧
        integerEdgeKeep Q u eligible g L K extra n ∧
        integerEdgeKeep Q u eligible g L K extra m) := fun hh => he hh.2.1
    rw [directedIntegerEdge, ite_eq_right hf, ite_eq_right he]

lemma backward_edge_as_shift (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d q : ℕ) (n m : ℤ) :
    directedIntegerEdge Q u eligible g center L K extra h d q m n =
      if m = n + (SignedStep.mk false d q).displacement h then
        signedIntegerWeight Q u eligible g center L K extra h ⟨false, d, q⟩ n else 0 := by
  classical
  have hd : (SignedStep.mk false d q).displacement h = -(h * q * d : ℕ) := by
    simp [SignedStep.displacement, Nat.cast_mul]
  rw [hd]
  by_cases he : m = n + -(h * q * d : ℕ)
  · subst m
    simp only [signedIntegerWeight, Bool.false_eq_true, ↓reduceIte, hd]
  · have hn : n ≠ m + (h * q * d : ℕ) := by omega
    have hf : ¬(q ∈ Q ∧ n = m + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ m ∧
        integerEdgeKeep Q u eligible g L K extra m ∧
        integerEdgeKeep Q u eligible g L K extra n) := fun hh => hn hh.2.1
    rw [directedIntegerEdge, ite_eq_right hf, ite_eq_right he]

lemma signedIntegerWeight_nonzero (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h : ℕ) (a : SignedStep) (n : ℤ)
    (ha : signedIntegerWeight Q u eligible g center L K extra h a n ≠ 0) :
    a.padding ∈ Q ∧ eligible a.padding ∧ (a.padding : ℤ) ∣ n ∧
      integerEdgeKeep Q u eligible g L K extra n ∧
      integerEdgeKeep Q u eligible g L K extra (n + a.displacement h) := by
  classical
  rcases a with ⟨b, d, q⟩
  cases b
  · simp only [signedIntegerWeight, Bool.false_eq_true, ↓reduceIte] at ha
    unfold directedIntegerEdge at ha
    split_ifs at ha with he
    · refine ⟨he.1, he.2.2.1, ?_, he.2.2.2.2.2, he.2.2.2.2.1⟩
      exact (padding_dvd_along_edge h q d _ _ he.2.1).mpr he.2.2.2.1
    · contradiction
  · simp only [signedIntegerWeight, ↓reduceIte] at ha
    unfold directedIntegerEdge at ha
    split_ifs at ha with he
    · exact ⟨he.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩
    · contradiction

lemma integerEdgeMatrix_signed_shifts {V : Type*} [Fintype V]
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d : ℕ) (i j : V) :
    integerEdgeMatrix site Q u eligible g center L K extra h d i j =
      ∑ q : Q, ∑ b : Bool,
        if site j = site i + (SignedStep.mk b d q).displacement h then
          signedIntegerWeight Q u eligible g center L K extra h ⟨b, d, q⟩ (site i)
        else 0 := by
  classical
  rw [integerEdgeMatrix, ← sum_coe_sort Q]
  apply sum_congr rfl
  intro q _
  rw [Fintype.sum_bool, forward_edge_as_shift, backward_edge_as_shift]

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

def integerShiftNext (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (e : D × (Q × Bool)) (x : D × ℤ) : D × ℤ :=
  (e.1, x.2 + (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h)

noncomputable def integerShiftWeight (Q : Finset ℕ) (tuple : D → ℕ)
    (u : ℕ → ℝ) (eligible : D → ℕ → Prop) (g : ℤ → ℝ) (center : D → ℤ → ℝ)
    (L K : ℝ) (extra : D → ℤ → Prop) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (e : D × (Q × Bool)) (x : D × ℤ) : ℝ := by
  classical
  exact if x.1 ≠ e.1 ∧ gate e.1 x.2 (integerShiftNext Q tuple h e x).2 then
    signedIntegerWeight Q u (eligible e.1) g (center e.1) L K (extra e.1) h
      ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 else 0

omit [DecidableEq V] in
/-- The step index is the actual tuple label, padding divisor and sign.
The finite state records the preceding tuple and the integer site. -/
theorem block_integer_matrix_eq_shift
    (site : V → ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (u : ℕ → ℝ) (eligible : D → ℕ → Prop) (g : ℤ → ℝ) (center : D → ℤ → ℝ)
    (L K : ℝ) (extra : D → ℤ → Prop) (h : ℕ) (gate : D → ℤ → ℤ → Prop) :
    blockNonbacktrackingMatrix (fun d i j =>
      if gate d (site i) (site j) then
        integerEdgeMatrix site Q u (eligible d) g (center d) L K (extra d) h (tuple d) i j
      else 0) =
    shiftMatrix (fun x : D × V => (x.1, site x.2)) (integerShiftNext Q tuple h)
      (integerShiftWeight Q tuple u eligible g center L K extra h gate) := by
  classical
  ext x y
  change (if x.1 ≠ y.1 then
    (if gate y.1 (site x.2) (site y.2) then
      integerEdgeMatrix site Q u (eligible y.1) g (center y.1) L K (extra y.1) h
        (tuple y.1) x.2 y.2 else 0) else 0) =
    shiftMatrix (fun x : D × V => (x.1, site x.2)) (integerShiftNext Q tuple h)
      (integerShiftWeight Q tuple u eligible g center L K extra h gate) x y
  rw [shiftMatrix, Fintype.sum_prod_type]
  rw [sum_eq_single y.1]
  · rw [Fintype.sum_prod_type]
    have ht (q : Q) (b : Bool) :
        (if integerShiftNext Q tuple h (y.1, q, b) (x.1, site x.2) = (y.1, site y.2)
          then integerShiftWeight Q tuple u eligible g center L K extra h gate
            (y.1, q, b) (x.1, site x.2) else 0) =
        if x.1 ≠ y.1 ∧ gate y.1 (site x.2) (site y.2) then
          if site y.2 = site x.2 + (SignedStep.mk b (tuple y.1) q).displacement h then
            signedIntegerWeight Q u (eligible y.1) g (center y.1) L K (extra y.1) h
              ⟨b, tuple y.1, q⟩ (site x.2) else 0
        else 0 := by
      by_cases he : site y.2 = site x.2 + (SignedStep.mk b (tuple y.1) q).displacement h
      · simp only [integerShiftNext, ← he, ↓reduceIte]
        simp [integerShiftWeight, integerShiftNext, ← he]
      · simp [integerShiftNext, Ne.symm he, he]
    trans ∑ q : Q, ∑ b : Bool,
      if x.1 ≠ y.1 ∧ gate y.1 (site x.2) (site y.2) then
        if site y.2 = site x.2 + (SignedStep.mk b (tuple y.1) q).displacement h then
          signedIntegerWeight Q u (eligible y.1) g (center y.1) L K (extra y.1) h
            ⟨b, tuple y.1, q⟩ (site x.2) else 0
      else 0
    · by_cases hc : x.1 ≠ y.1 ∧ gate y.1 (site x.2) (site y.2)
      · rw [ite_eq_left hc.1, ite_eq_left hc.2]
        simp only [ite_eq_left hc]
        exact integerEdgeMatrix_signed_shifts site Q u (eligible y.1) g (center y.1)
          L K (extra y.1) h (tuple y.1) x.2 y.2
      · simp only [hc, ↓reduceIte, sum_const_zero]
        by_cases hd : x.1 ≠ y.1
        · have hg : ¬gate y.1 (site x.2) (site y.2) := fun hg => hc ⟨hd, hg⟩
          simp [hd, hg]
        · simp [hd]
    · apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro b _
      convert (ht q b).symm using 1
      split_ifs <;> rfl
  · intro d _ hd
    apply sum_eq_zero
    intro e _
    have hn : integerShiftNext Q tuple h (d, e) (x.1, site x.2) ≠ (y.1, site y.2) := by
      intro he
      exact hd (congrArg Prod.fst he)
    simp only [hn, ↓reduceIte]
  · simp

end TwoPointCorrelations

end OAI
