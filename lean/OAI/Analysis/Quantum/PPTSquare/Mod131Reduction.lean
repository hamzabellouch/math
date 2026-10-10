import OAI.Analysis.Quantum.PPTSquare.Mod131Data

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace ModularPencil
open ModularSupport PolynomialCertificate
namespace P131
attribute [local instance] ModularPencil.P131.primeFact
lemma matrix_reduce_row0 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 0 j = A 0 j := by decide +kernel
lemma matrix_reduce_row1 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 1 j = A 1 j := by decide +kernel
lemma matrix_reduce_row2 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 2 j = A 2 j := by decide +kernel
lemma matrix_reduce_row3 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 3 j = A 3 j := by decide +kernel
lemma matrix_reduce_row4 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 4 j = A 4 j := by decide +kernel
lemma matrix_reduce_row5 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 5 j = A 5 j := by decide +kernel
lemma matrix_reduce_row6 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 6 j = A 6 j := by decide +kernel
lemma matrix_reduce_row7 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 7 j = A 7 j := by decide +kernel
lemma matrix_reduce_row8 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 8 j = A 8 j := by decide +kernel
lemma matrix_reduce_row9 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 9 j = A 9 j := by decide +kernel
lemma matrix_reduce_row10 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 10 j = A 10 j := by decide +kernel
lemma matrix_reduce_row11 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 11 j = A 11 j := by decide +kernel
lemma matrix_reduce_row12 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 12 j = A 12 j := by decide +kernel
lemma matrix_reduce_row13 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 13 j = A 13 j := by decide +kernel
lemma matrix_reduce_row14 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 14 j = A 14 j := by decide +kernel
lemma matrix_reduce_row15 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 15 j = A 15 j := by decide +kernel
lemma matrix_reduce_row16 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 16 j = A 16 j := by decide +kernel
lemma matrix_reduce_row17 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 17 j = A 17 j := by decide +kernel
lemma matrix_reduce_row18 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 18 j = A 18 j := by decide +kernel
lemma matrix_reduce_row19 : ∀ j : Fin 20, (N0Num.map (Int.castRingHom (ZMod 131))) 19 j = A 19 j := by decide +kernel
lemma matrix_reduce : N0Num.map (Int.castRingHom (ZMod 131)) = A := by
  ext i j
  fin_cases i
  · exact matrix_reduce_row0 j
  · exact matrix_reduce_row1 j
  · exact matrix_reduce_row2 j
  · exact matrix_reduce_row3 j
  · exact matrix_reduce_row4 j
  · exact matrix_reduce_row5 j
  · exact matrix_reduce_row6 j
  · exact matrix_reduce_row7 j
  · exact matrix_reduce_row8 j
  · exact matrix_reduce_row9 j
  · exact matrix_reduce_row10 j
  · exact matrix_reduce_row11 j
  · exact matrix_reduce_row12 j
  · exact matrix_reduce_row13 j
  · exact matrix_reduce_row14 j
  · exact matrix_reduce_row15 j
  · exact matrix_reduce_row16 j
  · exact matrix_reduce_row17 j
  · exact matrix_reduce_row18 j
  · exact matrix_reduce_row19 j
lemma first_column : ∀ i : Fin 20, U i 0 = (Pi.single 0 1 : Fin 20 → ZMod 131) i := by decide +kernel
lemma UV_row0 : ∀ j : Fin 20, U 0 j.castSucc = V 0 j := by intro j; fin_cases j <;> rfl
lemma UV_row1 : ∀ j : Fin 20, U 1 j.castSucc = V 1 j := by intro j; fin_cases j <;> rfl
lemma UV_row2 : ∀ j : Fin 20, U 2 j.castSucc = V 2 j := by intro j; fin_cases j <;> rfl
lemma UV_row3 : ∀ j : Fin 20, U 3 j.castSucc = V 3 j := by intro j; fin_cases j <;> rfl
lemma UV_row4 : ∀ j : Fin 20, U 4 j.castSucc = V 4 j := by intro j; fin_cases j <;> rfl
lemma UV_row5 : ∀ j : Fin 20, U 5 j.castSucc = V 5 j := by intro j; fin_cases j <;> rfl
lemma UV_row6 : ∀ j : Fin 20, U 6 j.castSucc = V 6 j := by intro j; fin_cases j <;> rfl
lemma UV_row7 : ∀ j : Fin 20, U 7 j.castSucc = V 7 j := by intro j; fin_cases j <;> rfl
lemma UV_row8 : ∀ j : Fin 20, U 8 j.castSucc = V 8 j := by intro j; fin_cases j <;> rfl
lemma UV_row9 : ∀ j : Fin 20, U 9 j.castSucc = V 9 j := by intro j; fin_cases j <;> rfl
lemma UV_row10 : ∀ j : Fin 20, U 10 j.castSucc = V 10 j := by intro j; fin_cases j <;> rfl
lemma UV_row11 : ∀ j : Fin 20, U 11 j.castSucc = V 11 j := by intro j; fin_cases j <;> rfl
lemma UV_row12 : ∀ j : Fin 20, U 12 j.castSucc = V 12 j := by intro j; fin_cases j <;> rfl
lemma UV_row13 : ∀ j : Fin 20, U 13 j.castSucc = V 13 j := by intro j; fin_cases j <;> rfl
lemma UV_row14 : ∀ j : Fin 20, U 14 j.castSucc = V 14 j := by intro j; fin_cases j <;> rfl
lemma UV_row15 : ∀ j : Fin 20, U 15 j.castSucc = V 15 j := by intro j; fin_cases j <;> rfl
lemma UV_row16 : ∀ j : Fin 20, U 16 j.castSucc = V 16 j := by intro j; fin_cases j <;> rfl
lemma UV_row17 : ∀ j : Fin 20, U 17 j.castSucc = V 17 j := by intro j; fin_cases j <;> rfl
lemma UV_row18 : ∀ j : Fin 20, U 18 j.castSucc = V 18 j := by intro j; fin_cases j <;> rfl
lemma UV_row19 : ∀ j : Fin 20, U 19 j.castSucc = V 19 j := by intro j; fin_cases j <;> rfl
lemma UV : U.submatrix id Fin.castSucc = V := by
  ext i j
  fin_cases i
  · exact UV_row0 j
  · exact UV_row1 j
  · exact UV_row2 j
  · exact UV_row3 j
  · exact UV_row4 j
  · exact UV_row5 j
  · exact UV_row6 j
  · exact UV_row7 j
  · exact UV_row8 j
  · exact UV_row9 j
  · exact UV_row10 j
  · exact UV_row11 j
  · exact UV_row12 j
  · exact UV_row13 j
  · exact UV_row14 j
  · exact UV_row15 j
  · exact UV_row16 j
  · exact UV_row17 j
  · exact UV_row18 j
  · exact UV_row19 j
end P131
end ModularPencil

end

end OAI
