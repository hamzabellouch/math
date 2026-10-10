import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_12 : ∀ k : Fin 48,
    fixedLiteralBaseMod (12 : Fin 48).castSucc k +
      fixedLiteralBaseMod (12 : Fin 48).succ k = fixedLiteralModPlus 12 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_12 : ∀ k : Fin 48,
    fixedLiteralBaseMod (12 : Fin 48).castSucc k -
      fixedLiteralBaseMod (12 : Fin 48).succ k = fixedLiteralModMinus 12 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_13 : ∀ k : Fin 48,
    fixedLiteralBaseMod (13 : Fin 48).castSucc k +
      fixedLiteralBaseMod (13 : Fin 48).succ k = fixedLiteralModPlus 13 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_13 : ∀ k : Fin 48,
    fixedLiteralBaseMod (13 : Fin 48).castSucc k -
      fixedLiteralBaseMod (13 : Fin 48).succ k = fixedLiteralModMinus 13 k := by
  decide +kernel

end InternalCatalan

end

end OAI
