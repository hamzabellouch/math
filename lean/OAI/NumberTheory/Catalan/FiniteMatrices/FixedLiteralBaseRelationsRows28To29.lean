import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_28 : ∀ k : Fin 48,
    fixedLiteralBaseMod (28 : Fin 48).castSucc k +
      fixedLiteralBaseMod (28 : Fin 48).succ k = fixedLiteralModPlus 28 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_28 : ∀ k : Fin 48,
    fixedLiteralBaseMod (28 : Fin 48).castSucc k -
      fixedLiteralBaseMod (28 : Fin 48).succ k = fixedLiteralModMinus 28 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_29 : ∀ k : Fin 48,
    fixedLiteralBaseMod (29 : Fin 48).castSucc k +
      fixedLiteralBaseMod (29 : Fin 48).succ k = fixedLiteralModPlus 29 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_29 : ∀ k : Fin 48,
    fixedLiteralBaseMod (29 : Fin 48).castSucc k -
      fixedLiteralBaseMod (29 : Fin 48).succ k = fixedLiteralModMinus 29 k := by
  decide +kernel

end InternalCatalan

end

end OAI
