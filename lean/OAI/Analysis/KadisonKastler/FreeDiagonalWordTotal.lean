import OAI.Analysis.KadisonKastler.FreeDiagonalGNS

namespace OAI

/-! # Totality of reduced centered words in the tracial Hilbert space -/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {r d : ℕ} (τ : FaithfulTracialState B) (e : Fin r → Fin d → B)

def diagonalWordVectorSpan : Submodule ℂ (TraceStateHilbert τ) :=
  Submodule.span ℂ {z | ∃ w, ReducedDiagonalWord w ∧ z = traceStateVector τ (diagonalWord e w)}

omit [PartialOrder B] [StarOrderedRing B] in
theorem reducedDiagonalSpan_dense
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (hgen : generatedDiagonal e = ⊤) : Dense (reducedDiagonalSpan e : Set B) := by
  intro x
  change x ∈ ((reducedDiagonalAlgebra e hp ho).topologicalClosure : Set B)
  rw [← generatedDiagonal_eq_reducedClosure e hp ho, hgen]
  trivial

theorem traceStateVector_mem_diagonalWordVectorSpan
    {x : B} (hx : x ∈ reducedDiagonalSpan e) :
    traceStateVector τ x ∈ diagonalWordVectorSpan τ e := by
  change traceStateVectorLinear τ x ∈ diagonalWordVectorSpan τ e
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  | zero => simpa only [map_zero] using (diagonalWordVectorSpan τ e).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (diagonalWordVectorSpan τ e).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (diagonalWordVectorSpan τ e).smul_mem c ih

theorem diagonalWordVectorSpan_total
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (hgen : generatedDiagonal e = ⊤) :
    (diagonalWordVectorSpan τ e).topologicalClosure = ⊤ := by
  have hc : Continuous (traceStateVector τ) := (traceStateVectorContinuous τ).continuous
  have hd := (traceStateVector_dense τ).dense_image hc (reducedDiagonalSpan_dense e hp ho hgen)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mp
  apply hd.mono
  rintro z ⟨x, hx, rfl⟩
  exact traceStateVector_mem_diagonalWordVectorSpan τ e hx

end

end KadisonKastler

end OAI
