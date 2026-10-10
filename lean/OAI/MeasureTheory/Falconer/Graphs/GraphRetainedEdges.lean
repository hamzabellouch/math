import OAI.MeasureTheory.Falconer.Graphs.GraphActualNonedgeSum

namespace OAI

namespace PlanarFalconer
open Set

noncomputable def graphChosenRepresentative {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (distance plus : Bool) (axis : ℝ) (j k : ℕ) : UnitCircle × UnitCircle := by
  classical
  exact if hs : (tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty then
    Classical.choose (graphSourceRepresentative_exists hδ hcap distance plus axis j k hs)
  else (sourceUnitDirection 0,sourceUnitDirection 0)

theorem graphChosenRepresentative_spec {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (distance plus : Bool) (axis : ℝ) (j k : ℕ) :
    GraphSourceRepresentative distance plus axis δ j k (graphChosenRepresentative hδ hcap distance plus axis j k) ∨
      ¬(tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty := by
  classical
  by_cases hs : (tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty
  · left
    simpa only [graphChosenRepresentative,dite_eq_left hs] using
      Classical.choose_spec (graphSourceRepresentative_exists hδ hcap distance plus axis j k hs)
  · exact Or.inr hs

def GraphRetainedEdge (N : ℕ) (sig p : ℝ) (distance plus : Bool)
    (P : Fin 4 → DyadicSquare) (q : UnitCircle × UnitCircle) : Prop :=
  ‖graphA (graphRepresentativeZ distance plus q) ((P 0).center-(P 1).center)+
    graphSourceSign distance plus • graphB (graphRepresentativeZ distance plus q) ((P 2).center-(P 3).center)‖ ≤
      graphNonedgeThreshold N sig p ∧
  (distance = false → |inner ℝ (graphRepresentativeAxis distance plus q)
    (graphDerivative (graphSourceSign distance plus) ((P 0).center-(P 1).center)
      ((P 2).center-(P 3).center))| ≤ graphNonedgeThreshold N sig p)

noncomputable def graphRetainedIndices (I : Finset GraphNonedgeIndex) (N : ℕ) (sig p : ℝ)
    (distance : Bool) (Q : Fin 4 → DyadicSquare) (q : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) :
    Finset GraphNonedgeIndex := by
  classical
  exact I.filter (fun e => GraphRetainedEdge N sig p distance e.2.2 (graphQuadCells Q e.1) (q e.2))

theorem graph_nonedge_of_not_retained (N : ℕ) (sig p : ℝ) (distance plus : Bool)
    (P : Fin 4 → DyadicSquare) (q : UnitCircle × UnitCircle)
    (hf : ¬GraphRetainedEdge N sig p distance plus P q) :
    GraphNonedge N sig p (graphSourceSign distance plus) (graphRepresentativeZ distance plus q)
      (graphRepresentativeAxis distance plus q) ((P 0).center-(P 1).center) ((P 2).center-(P 3).center) := by
  classical
  unfold GraphRetainedEdge at hf
  rcases not_and_or.mp hf with hvec | hscalar
  · exact Or.inl (not_le.mp hvec)
  · have hs := not_forall.mp hscalar
    obtain ⟨_,hs⟩ := hs
    exact Or.inr (not_le.mp hs)

theorem graph_sum_minus_retained (I : Finset GraphNonedgeIndex) (keep : GraphNonedgeIndex → Prop)
    [DecidablePred keep] (F : GraphNonedgeIndex → ℂ) (outer coeff : ℝ) :
    outer • (coeff • (∑ e ∈ I, F e)) - outer • (coeff • (∑ e ∈ I.filter keep, F e)) =
      outer • (coeff • (∑ e ∈ I.filter (fun e => ¬keep e), F e)) := by
  have he := Finset.sum_filter_add_sum_filter_not I keep F
  rw [← he,smul_add,smul_add,add_sub_cancel_left]

end PlanarFalconer

end OAI
