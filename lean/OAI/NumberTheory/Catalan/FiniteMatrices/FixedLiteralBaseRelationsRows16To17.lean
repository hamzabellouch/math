import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_16 : ∀ k : Fin 48,
    fixedLiteralBaseMod (16 : Fin 48).castSucc k +
      fixedLiteralBaseMod (16 : Fin 48).succ k = fixedLiteralModPlus 16 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_16 : ∀ k : Fin 48,
    fixedLiteralBaseMod (16 : Fin 48).castSucc k -
      fixedLiteralBaseMod (16 : Fin 48).succ k = fixedLiteralModMinus 16 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_17 : ∀ k : Fin 48,
    fixedLiteralBaseMod (17 : Fin 48).castSucc k +
      fixedLiteralBaseMod (17 : Fin 48).succ k = fixedLiteralModPlus 17 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_17 : ∀ k : Fin 48,
    fixedLiteralBaseMod (17 : Fin 48).castSucc k -
      fixedLiteralBaseMod (17 : Fin 48).succ k = fixedLiteralModMinus 17 k := by
  decide +kernel

end InternalCatalan

end

end OAI
