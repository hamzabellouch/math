import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_20 : ∀ k : Fin 48,
    fixedLiteralBaseMod (20 : Fin 48).castSucc k +
      fixedLiteralBaseMod (20 : Fin 48).succ k = fixedLiteralModPlus 20 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_20 : ∀ k : Fin 48,
    fixedLiteralBaseMod (20 : Fin 48).castSucc k -
      fixedLiteralBaseMod (20 : Fin 48).succ k = fixedLiteralModMinus 20 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_21 : ∀ k : Fin 48,
    fixedLiteralBaseMod (21 : Fin 48).castSucc k +
      fixedLiteralBaseMod (21 : Fin 48).succ k = fixedLiteralModPlus 21 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_21 : ∀ k : Fin 48,
    fixedLiteralBaseMod (21 : Fin 48).castSucc k -
      fixedLiteralBaseMod (21 : Fin 48).succ k = fixedLiteralModMinus 21 k := by
  decide +kernel

end InternalCatalan

end

end OAI
