import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_14 : ∀ k : Fin 48,
    fixedLiteralBaseMod (14 : Fin 48).castSucc k +
      fixedLiteralBaseMod (14 : Fin 48).succ k = fixedLiteralModPlus 14 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_14 : ∀ k : Fin 48,
    fixedLiteralBaseMod (14 : Fin 48).castSucc k -
      fixedLiteralBaseMod (14 : Fin 48).succ k = fixedLiteralModMinus 14 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_15 : ∀ k : Fin 48,
    fixedLiteralBaseMod (15 : Fin 48).castSucc k +
      fixedLiteralBaseMod (15 : Fin 48).succ k = fixedLiteralModPlus 15 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_15 : ∀ k : Fin 48,
    fixedLiteralBaseMod (15 : Fin 48).castSucc k -
      fixedLiteralBaseMod (15 : Fin 48).succ k = fixedLiteralModMinus 15 k := by
  decide +kernel

end InternalCatalan

end

end OAI
