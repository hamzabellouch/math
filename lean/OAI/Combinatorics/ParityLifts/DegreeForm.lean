import OAI.Combinatorics.ParityLifts.Degree

namespace OAI

namespace ParityWL.Complexity
lemma PolyProgram.mapWith_degree {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α × γ → β} (P : PolyProgram (α × γ) β f) :
    P.mapWith.degree = 468*P.degree^2+1950*P.degree+2184 := by
  simp only [PolyProgram.mapWith,PolyProgram.congr_degree,PolyProgram.comp_degree,
    PolyProgram.pair_degree,PolyProgram.foldlBounded_degree,PolyProgram.fst_degree,
    PolyProgram.snd_degree,PolyProgram.const_degree,PolyProgram.cons,PolyProgram.expr,
    PolyProgram.of_linear,PolyProgram.reverse_degree]
  ring_nf
lemma PolyProgram.filter_degree {α : Type} [TreeCodec α] {f : α → Bool} (P : PolyProgram α Bool f) :
    P.filter.degree = 260+52*P.degree := by
  simp only [PolyProgram.filter,PolyProgram.congr_degree,PolyProgram.comp_degree,
    PolyProgram.pair_degree,PolyProgram.foldlGrowing_degree,PolyProgram.fst_degree,
    PolyProgram.snd_degree,PolyProgram.const_degree,PolyProgram.cons,PolyProgram.expr,
    PolyProgram.of_linear,PolyProgram.reverse_degree,PolyProgram.ite_degree,PolyProgram.id_degree]
  ring_nf
lemma PolyProgram.any_degree {α : Type} [TreeCodec α] {f : α → Bool} (P : PolyProgram α Bool f) :
    P.any.degree = 14+4*P.degree := by
  simp only [PolyProgram.any,PolyProgram.congr_degree,PolyProgram.comp_degree,
    PolyProgram.pair_degree,PolyProgram.foldlBounded_degree,PolyProgram.fst_degree,
    PolyProgram.snd_degree,PolyProgram.const_degree,PolyProgram.or,PolyProgram.expr,
    PolyProgram.of_linear,PolyProgram.id_degree]
  ring_nf
end ParityWL.Complexity

end OAI
