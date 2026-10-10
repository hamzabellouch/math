import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_22 : ∀ k : Fin 48,
    fixedLiteralBaseMod (22 : Fin 48).castSucc k +
      fixedLiteralBaseMod (22 : Fin 48).succ k = fixedLiteralModPlus 22 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_22 : ∀ k : Fin 48,
    fixedLiteralBaseMod (22 : Fin 48).castSucc k -
      fixedLiteralBaseMod (22 : Fin 48).succ k = fixedLiteralModMinus 22 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_23 : ∀ k : Fin 48,
    fixedLiteralBaseMod (23 : Fin 48).castSucc k +
      fixedLiteralBaseMod (23 : Fin 48).succ k = fixedLiteralModPlus 23 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_23 : ∀ k : Fin 48,
    fixedLiteralBaseMod (23 : Fin 48).castSucc k -
      fixedLiteralBaseMod (23 : Fin 48).succ k = fixedLiteralModMinus 23 k := by
  decide +kernel

end InternalCatalan

end

end OAI
