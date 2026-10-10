import Mathlib
import OAI.Combinatorics.KMedian.Hardness.ProjectionInput
import OAI.Combinatorics.KMedian.Projection.Input
import OAI.Combinatorics.KMedian.Projection.Reindex
import OAI.Combinatorics.KMedian.Projection.Repeat

namespace OAI

section Inline_PCPProjectionToInput

namespace MetricKMedian.PCP.BiProjection
open scoped Classical

variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)
noncomputable def indexed := G.reindex (Fintype.equivFin U) (Fintype.equivFin V)
  (Fintype.equivFin D) (Fintype.equivFin S) (Fintype.equivFin A) (Fintype.equivFin B)
omit [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma indexed_consistent (hc : G.Consistent) : G.indexed.Consistent := G.reindex_consistent _ _ _ _ _ _ hc
noncomputable def toInput (hc : G.Consistent) : Coverage.ProjectionInput (Fintype.card S) (Fintype.card A) (Fintype.card B) :=
  G.indexed.input Fintype.card_pos Fintype.card_pos Fintype.card_pos Fintype.card_pos Fintype.card_pos (G.indexed_consistent hc)
omit [Nonempty D] in
lemma toInput_perfect (hc : G.Consistent) (h : G.Perfect) : (G.toInput hc).Perfect :=
  G.indexed.input_perfect _ _ _ _ _ _ (G.reindex_perfect _ _ _ _ _ _ h)
omit [Nonempty D] in
lemma toInput_sound (hc : G.Consistent) {ε : ℝ} (h : G.Sound ε) : (G.toInput hc).Sound ε :=
  G.indexed.input_sound _ _ _ _ _ _ (G.reindex_sound _ _ _ _ _ _ h)
omit [Nonempty D] in
lemma toInput_u (hc : G.Consistent) : (G.toInput hc).u=Fintype.card U := rfl
omit [Nonempty D] in
lemma toInput_v (hc : G.Consistent) : (G.toInput hc).v=Fintype.card V := rfl
omit [Nonempty D] in
lemma toInput_degree (hc : G.Consistent) : (G.toInput hc).degree=Fintype.card D := rfl
end MetricKMedian.PCP.BiProjection

end Inline_PCPProjectionToInput

end OAI
