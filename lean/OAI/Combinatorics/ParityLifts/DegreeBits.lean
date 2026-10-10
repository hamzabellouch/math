import OAI.Combinatorics.ParityLifts.DegreeGraph

namespace OAI

namespace ParityWL.Complexity
attribute [local simp] PolyProgram.congr_degree PolyProgram.comp_degree PolyProgram.pair_degree
  PolyProgram.ite_degree PolyProgram.const_degree PolyProgram.id_degree PolyProgram.fst_degree
  PolyProgram.snd_degree PolyProgram.equal_degree PolyProgram.foldlGrowing_degree
  PolyProgram.foldlBounded_degree PolyProgram.map_degree PolyProgram.reverse_degree
  PolyProgram.mapWith_degree PolyProgram.filter_degree PolyProgram.any_degree
  PolyProgram.expr PolyProgram.of_linear PolyProgram.finite_degree PolyProgram.finite2_degree
  PolyProgram.evalFin_degree PolyProgram.length_degree

lemma PolyProgram.tabulate_degree {α β : Type} [TreeCodec α] [TreeCodec β] {n : ℕ}
    {f : Fin n × α → β} (P : PolyProgram (Fin n × α) β f) :
    P.tabulate.degree=2+2*(468*P.degree^2+1950*P.degree+2184) := by
  unfold PolyProgram.tabulate PolyProgram.recode
  simp
attribute [local simp] PolyProgram.tabulate_degree
lemma PolyProgram.groupAt_degree (t : ℕ) :
    (PolyProgram.groupAt t).degree=(PolyProgram.groupAt 1).degree := by
  simp only [PolyProgram.groupAt]; simp
attribute [local simp] PolyProgram.groupAt_degree
lemma PolyProgram.pairKey_degree (t : ℕ) :
    (PolyProgram.pairKey t).degree=(PolyProgram.pairKey 1).degree := by
  unfold PolyProgram.pairKey
  erw [PolyProgram.congr_degree,PolyProgram.congr_degree]
  simp
attribute [local simp] PolyProgram.pairKey_degree
lemma PolyProgram.rowKeyWith_degree (t : ℕ) :
    (PolyProgram.rowKeyWith t).degree=(PolyProgram.rowKeyWith 1).degree := by
  unfold PolyProgram.rowKeyWith
  simp
attribute [local simp] PolyProgram.rowKeyWith_degree
lemma PolyProgram.domainWith_degree (t : ℕ) :
    (PolyProgram.domainWith t).degree=(PolyProgram.domainWith 1).degree := by
  unfold PolyProgram.domainWith
  erw [PolyProgram.congr_degree,PolyProgram.congr_degree]
  simp
attribute [local simp] PolyProgram.domainWith_degree
lemma PolyProgram.choiceWithWords_degree (t : ℕ) :
    (PolyProgram.choiceWithWords t).degree=(PolyProgram.choiceWithWords 1).degree := by
  unfold PolyProgram.choiceWithWords
  erw [PolyProgram.congr_degree,PolyProgram.congr_degree]
  simp
end ParityWL.Complexity

end OAI
