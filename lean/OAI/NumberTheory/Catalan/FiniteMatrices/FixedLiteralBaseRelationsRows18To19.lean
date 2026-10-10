import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_18 : ∀ k : Fin 48,
    fixedLiteralBaseMod (18 : Fin 48).castSucc k +
      fixedLiteralBaseMod (18 : Fin 48).succ k = fixedLiteralModPlus 18 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_18 : ∀ k : Fin 48,
    fixedLiteralBaseMod (18 : Fin 48).castSucc k -
      fixedLiteralBaseMod (18 : Fin 48).succ k = fixedLiteralModMinus 18 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_19 : ∀ k : Fin 48,
    fixedLiteralBaseMod (19 : Fin 48).castSucc k +
      fixedLiteralBaseMod (19 : Fin 48).succ k = fixedLiteralModPlus 19 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_19 : ∀ k : Fin 48,
    fixedLiteralBaseMod (19 : Fin 48).castSucc k -
      fixedLiteralBaseMod (19 : Fin 48).succ k = fixedLiteralModMinus 19 k := by
  decide +kernel

end InternalCatalan

end

end OAI
