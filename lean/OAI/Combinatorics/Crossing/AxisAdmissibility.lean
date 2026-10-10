import OAI.Combinatorics.Crossing.AxisFiniteCrossings
import OAI.Combinatorics.Crossing.AxisGenericPositions
import OAI.Combinatorics.Crossing.RowCrossingCount

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem axisContinuousDrawing_meeting_independent (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (x : Plane) (hx : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e)
    (hy : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) f) : e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  rw [axisContinuousDrawing_interior] at hx hy
  obtain ⟨t,ht,he⟩ := hx
  obtain ⟨u,hu,hf⟩ := hy
  have hmeet : axisSegmentPoint (a e.1) (b e.2) t=axisSegmentPoint (a f.1) (b f.2) u := he.trans hf.symm
  constructor
  · intro hfirst
    rw [hfirst] at hmeet
    have hh := axisSegmentPoint_same_vertical (a f.1) (b e.2) (b f.2) t u (ha f.1) ht.1 hmeet
    exact hef (Prod.ext hfirst (hbi hh))
  · intro hsecond
    rw [hsecond] at hmeet
    have hh := axisSegmentPoint_same_horizontal (a e.1) (a f.1) (b f.2) t u (hb f.2) ht.2 hmeet
    exact hef (Prod.ext (hai hh) hsecond)

theorem axisContinuousDrawing_line_equation (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e : BipartiteEdge m n) (x : Plane)
    (hx : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e) :
    a e.1*x.1+b e.2*x.2=a e.1*b e.2 := by
  rw [axisContinuousDrawing_interior] at hx
  obtain ⟨t,ht,he⟩ := hx
  rw [← he]
  exact axisSegmentPoint_line_equation _ _ _

def axisAdmissibleDrawing (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0)
    (hgeneric : ∀ e f g : BipartiteEdge m n, AxisIndependentTriple e f g →
      axisConcurrency (a e.1) (b e.2) (a f.1) (b f.2) (a g.1) (b g.2) ≠ 0) : AdmissibleDrawing m n where
  toContinuousDrawing := axisContinuousDrawing a b hai hbi ha hb
  crossings_finite := axisContinuousDrawing_crossings_finite a b hai hbi ha hb
  crossings_proper := axisContinuousDrawing_crossings_proper a b hai hbi ha hb
  no_triples := by
    intro e f g hef heg hfg
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨he,hf⟩,hg⟩
    have h₀ := axisContinuousDrawing_meeting_independent a b hai hbi ha hb e f hef x he hf
    have h₁ := axisContinuousDrawing_meeting_independent a b hai hbi ha hb e g heg x he hg
    have h₂ := axisContinuousDrawing_meeting_independent a b hai hbi ha hb f g hfg x hf hg
    exact hgeneric e f g ⟨h₀.1,h₁.1,h₂.1,h₀.2,h₁.2,h₂.2⟩
      (axisConcurrency_zero_of_meeting _ _ _ _ _ _ x
        (axisContinuousDrawing_line_equation a b hai hbi ha hb e x he)
        (axisContinuousDrawing_line_equation a b hai hbi ha hb f x hf)
        (axisContinuousDrawing_line_equation a b hai hbi ha hb g x hg))

theorem axisAdmissibleDrawing_noAdjacent (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0)
    (hgeneric : ∀ e f g : BipartiteEdge m n, AxisIndependentTriple e f g →
      axisConcurrency (a e.1) (b e.2) (a f.1) (b f.2) (a g.1) (b g.2) ≠ 0) :
    NoAdjacentCrossings (axisAdmissibleDrawing a b hai hbi ha hb hgeneric) := by
  intro e f hef hadj
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx,hy⟩
  have hh := axisContinuousDrawing_meeting_independent a b hai hbi ha hb e f hef x hx hy
  exact hadj.elim hh.1 hh.2

end Zarankiewicz

end

end OAI
