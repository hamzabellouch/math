import OAI.NumberTheory.TwoPoint.Bounds.IntegerPathProduct
import OAI.NumberTheory.TwoPoint.Bounds.IntegerClosedCatalog

namespace OAI

/-! Separate literal vertex deletion from the numerical copy and block gates. -/

namespace TwoPointCorrelations

open scoped Classical

variable {D V : Type*}

def integerVertexGate (gate : D → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (d : D) (n m : ℤ) : Prop := gate d n m ∧ keep n ∧ keep m

noncomputable def vertexIndicator (keep : ℤ → Prop) (n : ℤ) : ℝ :=
  if keep n then 1 else 0

lemma integerStepMask_vertex (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (h : ℕ) (gate : D → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : D × (Q × Bool)) (x : D × ℤ) :
    integerStepMask embed Q tuple h (integerVertexGate gate keep) e x =
      integerStepMask embed Q tuple h gate e x *
        (vertexIndicator keep x.2 * vertexIndicator keep (integerShiftNext Q tuple h e x).2) := by
  by_cases hc : x.1 ≠ e.1 ∧ gate e.1 x.2 (integerShiftNext Q tuple h e x).2 ∧
      integerShiftNext Q tuple h e x ∈ Set.range embed
  · by_cases hx : keep x.2 <;> by_cases hy : keep (integerShiftNext Q tuple h e x).2 <;>
      simp [integerStepMask, integerVertexGate, vertexIndicator, hc.1, hc.2.1, hc.2.2, hx, hy]
  · have hbad : ¬(x.1 ≠ e.1 ∧
        integerVertexGate gate keep e.1 x.2 (integerShiftNext Q tuple h e x).2 ∧
        integerShiftNext Q tuple h e x ∈ Set.range embed) := by
      rintro ⟨hcopy, hgate, hrange⟩
      exact hc ⟨hcopy, hgate.1, hrange⟩
    simp only [integerStepMask, ite_eq_right hc, ite_eq_right hbad, zero_mul]

theorem integerPathMask_vertex (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (h : ℕ) (gate : D → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    {k : ℕ} (x : D × ℤ) (w : Fin k → D × (Q × Bool)) :
    integerPathMask embed Q tuple h (integerVertexGate gate keep) x w =
      integerPathMask embed Q tuple h gate x w *
        scalarWalkProduct h (fun t n => vertexIndicator keep n *
          vertexIndicator keep (n + t.displacement h)) x.2 (integerStepWord Q tuple w) := by
  induction k generalizing x with
  | zero => simp [integerPathMask, integerStepWord, scalarWalkProduct]
  | succ k ih =>
      rw [integerPathMask, integerStepMask_vertex, ih]
      simp only [integerPathMask, integerStepWord, List.ofFn_succ, List.map_cons, scalarWalkProduct]
      dsimp only [integerShiftNext, Fin.tail_def]
      ring

lemma vertex_edge_flip (h : ℕ) (keep : ℤ → Prop) (t : SignedStep) (n : ℤ) :
    (vertexIndicator keep (n + t.displacement h) *
      vertexIndicator keep (n + t.displacement h + t.flip.displacement h)) =
      vertexIndicator keep n * vertexIndicator keep (n + t.displacement h) := by
  rw [SignedStep.displacement_flip]
  have he : n + t.displacement h + -t.displacement h = n := by ring
  rw [he, mul_comm]

theorem integerPathMask_closed_vertex_pair (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    {k : ℕ} (x : D × ℤ) (a b : Fin k → D × (Q × Bool))
    (hend : shiftWordEnd (integerShiftNext Q tuple h) x a =
      shiftWordEnd (integerShiftNext Q tuple h) x b) :
    integerPathMask embed Q tuple h (integerVertexGate gate keep) x a *
      integerPathMask embed Q tuple h (integerVertexGate gate keep) x b =
      (integerPathMask embed Q tuple h gate x a * integerPathMask embed Q tuple h gate x b) *
        scalarWalkProduct h (fun t n => vertexIndicator keep n *
          vertexIndicator keep (n + t.displacement h)) x.2
          (integerClosedWordCode Q tuple (a, b)) := by
  have he := congrArg (fun y : D × ℤ => y.2) hend
  rw [integerShiftEnd_site, integerShiftEnd_site] at he
  have hd : wordDisplacement h (integerStepWord Q tuple a) =
      wordDisplacement h (integerStepWord Q tuple b) := by omega
  rw [integerPathMask_vertex, integerPathMask_vertex]
  unfold integerClosedWordCode
  rw [← scalarWalkProduct_closed_pair h _ (vertex_edge_flip h keep) x.2 _ _ hd]
  ring

end TwoPointCorrelations

end OAI
