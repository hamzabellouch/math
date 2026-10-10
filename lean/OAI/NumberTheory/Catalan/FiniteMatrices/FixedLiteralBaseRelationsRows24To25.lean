import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_24 : ∀ k : Fin 48,
    fixedLiteralBaseMod (24 : Fin 48).castSucc k +
      fixedLiteralBaseMod (24 : Fin 48).succ k = fixedLiteralModPlus 24 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_24 : ∀ k : Fin 48,
    fixedLiteralBaseMod (24 : Fin 48).castSucc k -
      fixedLiteralBaseMod (24 : Fin 48).succ k = fixedLiteralModMinus 24 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_25 : ∀ k : Fin 48,
    fixedLiteralBaseMod (25 : Fin 48).castSucc k +
      fixedLiteralBaseMod (25 : Fin 48).succ k = fixedLiteralModPlus 25 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_25 : ∀ k : Fin 48,
    fixedLiteralBaseMod (25 : Fin 48).castSucc k -
      fixedLiteralBaseMod (25 : Fin 48).succ k = fixedLiteralModMinus 25 k := by
  decide +kernel

end InternalCatalan

end

end OAI
