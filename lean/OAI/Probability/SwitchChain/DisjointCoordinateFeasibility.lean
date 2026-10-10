import OAI.Probability.SwitchChain.DisjointRealization

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.CrossBlock

theorem total_eq_row_add (M : Matrix) : total M = row M 0 + row M 1 := by
  simp [total, Fin.sum_univ_two]

theorem total_eq_col_add (M : Matrix) : total M = col M 0 + col M 1 := by
  simp only [total, row, col, Fin.sum_univ_two]
  omega

end Problem315.CrossBlock

namespace Problem315.DisjointEncoding
variable {V : Type*} [Fintype V]

theorem coordinate_degrees_iff
    (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    (∀ a,
      (internalGraph (decide (G.Adj (e 0) (e 1)))
        (decide (G.Adj (e 2) (e 3))) M).degree a +
        (Finset.univ.filter (assignmentBoundary e G U W a)).card = G.degree (e a)) ↔
    CrossBlock.total M = CrossBlock.total (crossCode e G) ∧
      CrossBlock.row M 0 + U.card =
        CrossBlock.row (crossCode e G) 0 + (leftAssignment e G G).card ∧
      CrossBlock.col M 0 + W.card =
        CrossBlock.col (crossCode e G) 0 + (rightAssignment e G G).card := by
  let l := decide (G.Adj (e 0) (e 1))
  let r := decide (G.Adj (e 2) (e 3))
  let M₀ := crossCode e G
  let U₀ := leftAssignment e G G
  let W₀ := rightAssignment e G G
  have hU₀ : U₀ ⊆ BinaryAssignments.singletons (leftCounts e G) := Finset.filter_subset _ _
  have hW₀ : W₀ ⊆ BinaryAssignments.singletons (rightCounts e G) := Finset.filter_subset _ _
  have hbase := (cellEncode e G ⟨G, SameCell.refl e G, fun _ => rfl⟩).degrees
  change ∀ a, (internalGraph l r M₀).degree a +
    (Finset.univ.filter (assignmentBoundary e G U₀ W₀ a)).card = G.degree (e a) at hbase
  have hbase0 := hbase 0
  have hbase1 := hbase 1
  have hbase2 := hbase 2
  have hbase3 := hbase 3
  have hd0 := internalGraph_degree_left l r M 0
  have hd1 := internalGraph_degree_left l r M 1
  have hd2 := internalGraph_degree_right l r M 0
  have hd3 := internalGraph_degree_right l r M 1
  have hd00 := internalGraph_degree_left l r M₀ 0
  have hd01 := internalGraph_degree_left l r M₀ 1
  have hd02 := internalGraph_degree_right l r M₀ 0
  have hd03 := internalGraph_degree_right l r M₀ 1
  change (internalGraph l r M).degree 0 = _ at hd0
  change (internalGraph l r M).degree 1 = _ at hd1
  change (internalGraph l r M).degree 2 = _ at hd2
  change (internalGraph l r M).degree 3 = _ at hd3
  change (internalGraph l r M₀).degree 0 = _ at hd00
  change (internalGraph l r M₀).degree 1 = _ at hd01
  change (internalGraph l r M₀).degree 2 = _ at hd02
  change (internalGraph l r M₀).degree 3 = _ at hd03
  have hb0 := assignmentBoundary_card_zero e G U W hU
  have hb1 := assignmentBoundary_card_one e G U W hU
  have hb2 := assignmentBoundary_card_two e G U W hW
  have hb3 := assignmentBoundary_card_three e G U W hW
  have hb00 := assignmentBoundary_card_zero e G U₀ W₀ hU₀
  have hb01 := assignmentBoundary_card_one e G U₀ W₀ hU₀
  have hb02 := assignmentBoundary_card_two e G U₀ W₀ hW₀
  have hb03 := assignmentBoundary_card_three e G U₀ W₀ hW₀
  have ht := CrossBlock.total_eq_row_add M
  have ht₀ := CrossBlock.total_eq_row_add M₀
  have hc := CrossBlock.total_eq_col_add M
  have hc₀ := CrossBlock.total_eq_col_add M₀
  change (∀ a, (internalGraph l r M).degree a +
    (Finset.univ.filter (assignmentBoundary e G U W a)).card = G.degree (e a)) ↔
    CrossBlock.total M = CrossBlock.total M₀ ∧
      CrossBlock.row M 0 + U.card = CrossBlock.row M₀ 0 + U₀.card ∧
      CrossBlock.col M 0 + W.card = CrossBlock.col M₀ 0 + W₀.card
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega
  · rintro ⟨htotal, hleft, hright⟩ a
    have h0 : (internalGraph l r M).degree 0 +
        (Finset.univ.filter (assignmentBoundary e G U W 0)).card = G.degree (e 0) := by omega
    have h1 : (internalGraph l r M).degree 1 +
        (Finset.univ.filter (assignmentBoundary e G U W 1)).card = G.degree (e 1) := by omega
    have h2 : (internalGraph l r M).degree 2 +
        (Finset.univ.filter (assignmentBoundary e G U W 2)).card = G.degree (e 2) := by omega
    have h3 : (internalGraph l r M).degree 3 +
        (Finset.univ.filter (assignmentBoundary e G U W 3)).card = G.degree (e 3) := by omega
    fin_cases a
    · exact h0
    · exact h1
    · exact h2
    · exact h3

end Problem315.DisjointEncoding

end

end OAI
