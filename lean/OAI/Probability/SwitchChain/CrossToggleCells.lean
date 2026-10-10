import OAI.Probability.SwitchChain.CrossTogglePairs
import OAI.Probability.SwitchChain.DisjointCellGlobal

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SwitchFlip

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem projection_restrictCell_of_crosses (p : SwitchProposal n) (a : Finset (Fin n))
    (ha : SwitchPairFiber.Crosses p a) (C : GraphState n d → Prop)
    (hC : PairResampling.CellInvariant a C) (f : PairResampling.StateSpace n d) :
    projection p (PairResampling.restrictCell C f) =
      PairResampling.restrictCell C (projection p f) := by
  ext G
  have hCG : C G ↔ C (flip p G) := hC G (flip p G) (flip_sameFiber p a ha G)
  by_cases hG : C G
  · have hT := hCG.mp hG
    simp [projection_apply, PairResampling.restrictCell_apply, hG, hT]
  · have hT : ¬ C (flip p G) := fun h => hG (hCG.mpr h)
    simp [projection_apply, PairResampling.restrictCell_apply, hG, hT]

theorem projection_preserves_cell_support_of_crosses (p : SwitchProposal n) (a : Finset (Fin n))
    (ha : SwitchPairFiber.Crosses p a) (C : GraphState n d → Prop)
    (hC : PairResampling.CellInvariant a C) (f : PairResampling.StateSpace n d)
    (hf : ∀ G, ¬ C G → f G = 0) :
    ∀ G, ¬ C G → projection p f G = 0 := by
  apply (PairResampling.restrictCell_eq_self_iff C _).mp
  rw [← projection_restrictCell_of_crosses p a ha C hC,
    (PairResampling.restrictCell_eq_self_iff C f).mpr hf]

end Problem315.SwitchFlip

namespace Problem315.CrossToggle

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem pairProjection_restrictCell (a b : VertexPair n)
    (C : GraphState n d → Prop) (hC : PairResampling.CellInvariant a.val C)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b (PairResampling.restrictCell C f) =
      PairResampling.restrictCell C (pairProjection a b f) := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h]
    exact SwitchFlip.projection_restrictCell_of_crosses _ _ (pairProposal_crosses_left a b h) C hC f
  · simp only [pairProjection, dite_eq_right h, zero_apply]
    ext G
    simp [PairResampling.restrictCell_apply]

theorem pairProjection_norm_sq_eq_sum_cells {β : Type*} [Fintype β]
    (k : GraphState n d → β) (a b : VertexPair n)
    (ha : ∀ c, PairResampling.CellInvariant a.val (fun G => k G = c))
    (f : PairResampling.StateSpace n d) :
    ‖pairProjection a b f‖ ^ 2 = ∑ c : β,
      ‖pairProjection a b (PairResampling.restrictCell (fun G => k G = c) f)‖ ^ 2 := by
  exact PairResampling.map_norm_sq_eq_sum_cells k (pairProjection a b)
    (fun c g => pairProjection_restrictCell a b _ (ha c) g) f

end Problem315.CrossToggle

end

end OAI
