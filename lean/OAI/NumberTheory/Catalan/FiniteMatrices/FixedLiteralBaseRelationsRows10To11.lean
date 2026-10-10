import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_10 : ∀ k : Fin 48,
    fixedLiteralBaseMod (10 : Fin 48).castSucc k +
      fixedLiteralBaseMod (10 : Fin 48).succ k = fixedLiteralModPlus 10 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_10 : ∀ k : Fin 48,
    fixedLiteralBaseMod (10 : Fin 48).castSucc k -
      fixedLiteralBaseMod (10 : Fin 48).succ k = fixedLiteralModMinus 10 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_11 : ∀ k : Fin 48,
    fixedLiteralBaseMod (11 : Fin 48).castSucc k +
      fixedLiteralBaseMod (11 : Fin 48).succ k = fixedLiteralModPlus 11 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_11 : ∀ k : Fin 48,
    fixedLiteralBaseMod (11 : Fin 48).castSucc k -
      fixedLiteralBaseMod (11 : Fin 48).succ k = fixedLiteralModMinus 11 k := by
  decide +kernel

end InternalCatalan

end

end OAI
