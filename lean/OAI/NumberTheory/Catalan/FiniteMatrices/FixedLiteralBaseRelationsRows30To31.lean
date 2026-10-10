import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_30 : ∀ k : Fin 48,
    fixedLiteralBaseMod (30 : Fin 48).castSucc k +
      fixedLiteralBaseMod (30 : Fin 48).succ k = fixedLiteralModPlus 30 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_30 : ∀ k : Fin 48,
    fixedLiteralBaseMod (30 : Fin 48).castSucc k -
      fixedLiteralBaseMod (30 : Fin 48).succ k = fixedLiteralModMinus 30 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_31 : ∀ k : Fin 48,
    fixedLiteralBaseMod (31 : Fin 48).castSucc k +
      fixedLiteralBaseMod (31 : Fin 48).succ k = fixedLiteralModPlus 31 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_31 : ∀ k : Fin 48,
    fixedLiteralBaseMod (31 : Fin 48).castSucc k -
      fixedLiteralBaseMod (31 : Fin 48).succ k = fixedLiteralModMinus 31 k := by
  decide +kernel

end InternalCatalan

end

end OAI
