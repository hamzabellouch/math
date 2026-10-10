import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_26 : ∀ k : Fin 48,
    fixedLiteralBaseMod (26 : Fin 48).castSucc k +
      fixedLiteralBaseMod (26 : Fin 48).succ k = fixedLiteralModPlus 26 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_26 : ∀ k : Fin 48,
    fixedLiteralBaseMod (26 : Fin 48).castSucc k -
      fixedLiteralBaseMod (26 : Fin 48).succ k = fixedLiteralModMinus 26 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_27 : ∀ k : Fin 48,
    fixedLiteralBaseMod (27 : Fin 48).castSucc k +
      fixedLiteralBaseMod (27 : Fin 48).succ k = fixedLiteralModPlus 27 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_27 : ∀ k : Fin 48,
    fixedLiteralBaseMod (27 : Fin 48).castSucc k -
      fixedLiteralBaseMod (27 : Fin 48).succ k = fixedLiteralModMinus 27 k := by
  decide +kernel

end InternalCatalan

end

end OAI
