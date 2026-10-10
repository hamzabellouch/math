import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_2 : ∀ k : Fin 48,
    fixedLiteralBaseMod (2 : Fin 48).castSucc k +
      fixedLiteralBaseMod (2 : Fin 48).succ k = fixedLiteralModPlus 2 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_2 : ∀ k : Fin 48,
    fixedLiteralBaseMod (2 : Fin 48).castSucc k -
      fixedLiteralBaseMod (2 : Fin 48).succ k = fixedLiteralModMinus 2 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_3 : ∀ k : Fin 48,
    fixedLiteralBaseMod (3 : Fin 48).castSucc k +
      fixedLiteralBaseMod (3 : Fin 48).succ k = fixedLiteralModPlus 3 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_3 : ∀ k : Fin 48,
    fixedLiteralBaseMod (3 : Fin 48).castSucc k -
      fixedLiteralBaseMod (3 : Fin 48).succ k = fixedLiteralModMinus 3 k := by
  decide +kernel

end InternalCatalan

end

end OAI
