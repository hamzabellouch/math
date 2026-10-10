import OAI.Analysis.Quantum.PPTSquare.Mod131Reduction

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace ModularPencil
open ModularSupport PolynomialCertificate
namespace P131
attribute [local instance] ModularPencil.P131.primeFact
lemma B_V_row0 : ∀ j : Fin 20, (B * V) 0 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 0 j := by decide +kernel
lemma A_V_row0 : ∀ j : Fin 20, (A * V) 0 j = U 0 j.succ := by decide +kernel
lemma B_V_row1 : ∀ j : Fin 20, (B * V) 1 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 1 j := by decide +kernel
lemma A_V_row1 : ∀ j : Fin 20, (A * V) 1 j = U 1 j.succ := by decide +kernel
lemma B_V_row2 : ∀ j : Fin 20, (B * V) 2 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 2 j := by decide +kernel
lemma A_V_row2 : ∀ j : Fin 20, (A * V) 2 j = U 2 j.succ := by decide +kernel
lemma B_V_row3 : ∀ j : Fin 20, (B * V) 3 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 3 j := by decide +kernel
lemma A_V_row3 : ∀ j : Fin 20, (A * V) 3 j = U 3 j.succ := by decide +kernel
lemma B_V_row4 : ∀ j : Fin 20, (B * V) 4 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 4 j := by decide +kernel
lemma A_V_row4 : ∀ j : Fin 20, (A * V) 4 j = U 4 j.succ := by decide +kernel
lemma B_V_row5 : ∀ j : Fin 20, (B * V) 5 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 5 j := by decide +kernel
lemma A_V_row5 : ∀ j : Fin 20, (A * V) 5 j = U 5 j.succ := by decide +kernel
lemma B_V_row6 : ∀ j : Fin 20, (B * V) 6 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 6 j := by decide +kernel
lemma A_V_row6 : ∀ j : Fin 20, (A * V) 6 j = U 6 j.succ := by decide +kernel
lemma B_V_row7 : ∀ j : Fin 20, (B * V) 7 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 7 j := by decide +kernel
lemma A_V_row7 : ∀ j : Fin 20, (A * V) 7 j = U 7 j.succ := by decide +kernel
lemma B_V_row8 : ∀ j : Fin 20, (B * V) 8 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 8 j := by decide +kernel
lemma A_V_row8 : ∀ j : Fin 20, (A * V) 8 j = U 8 j.succ := by decide +kernel
lemma B_V_row9 : ∀ j : Fin 20, (B * V) 9 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 9 j := by decide +kernel
lemma A_V_row9 : ∀ j : Fin 20, (A * V) 9 j = U 9 j.succ := by decide +kernel
lemma B_V_row10 : ∀ j : Fin 20, (B * V) 10 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 10 j := by decide +kernel
lemma A_V_row10 : ∀ j : Fin 20, (A * V) 10 j = U 10 j.succ := by decide +kernel
lemma B_V_row11 : ∀ j : Fin 20, (B * V) 11 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 11 j := by decide +kernel
lemma A_V_row11 : ∀ j : Fin 20, (A * V) 11 j = U 11 j.succ := by decide +kernel
lemma B_V_row12 : ∀ j : Fin 20, (B * V) 12 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 12 j := by decide +kernel
lemma A_V_row12 : ∀ j : Fin 20, (A * V) 12 j = U 12 j.succ := by decide +kernel
lemma B_V_row13 : ∀ j : Fin 20, (B * V) 13 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 13 j := by decide +kernel
lemma A_V_row13 : ∀ j : Fin 20, (A * V) 13 j = U 13 j.succ := by decide +kernel
lemma B_V_row14 : ∀ j : Fin 20, (B * V) 14 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 14 j := by decide +kernel
lemma A_V_row14 : ∀ j : Fin 20, (A * V) 14 j = U 14 j.succ := by decide +kernel
lemma B_V_row15 : ∀ j : Fin 20, (B * V) 15 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 15 j := by decide +kernel
lemma A_V_row15 : ∀ j : Fin 20, (A * V) 15 j = U 15 j.succ := by decide +kernel
lemma B_V_row16 : ∀ j : Fin 20, (B * V) 16 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 16 j := by decide +kernel
lemma A_V_row16 : ∀ j : Fin 20, (A * V) 16 j = U 16 j.succ := by decide +kernel
lemma B_V_row17 : ∀ j : Fin 20, (B * V) 17 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 17 j := by decide +kernel
lemma A_V_row17 : ∀ j : Fin 20, (A * V) 17 j = U 17 j.succ := by decide +kernel
lemma B_V_row18 : ∀ j : Fin 20, (B * V) 18 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 18 j := by decide +kernel
lemma A_V_row18 : ∀ j : Fin 20, (A * V) 18 j = U 18 j.succ := by decide +kernel
lemma B_V_row19 : ∀ j : Fin 20, (B * V) 19 j = (1 : Matrix (Fin 20) (Fin 20) (ZMod 131)) 19 j := by decide +kernel
lemma A_V_row19 : ∀ j : Fin 20, (A * V) 19 j = U 19 j.succ := by decide +kernel
lemma B_V : B * V = 1 := by
  ext i j
  fin_cases i
  · exact B_V_row0 j
  · exact B_V_row1 j
  · exact B_V_row2 j
  · exact B_V_row3 j
  · exact B_V_row4 j
  · exact B_V_row5 j
  · exact B_V_row6 j
  · exact B_V_row7 j
  · exact B_V_row8 j
  · exact B_V_row9 j
  · exact B_V_row10 j
  · exact B_V_row11 j
  · exact B_V_row12 j
  · exact B_V_row13 j
  · exact B_V_row14 j
  · exact B_V_row15 j
  · exact B_V_row16 j
  · exact B_V_row17 j
  · exact B_V_row18 j
  · exact B_V_row19 j
lemma step : ∀ j : Fin 20, A.mulVec (fun i => U i j.castSucc) = fun i => U i j.succ := by
  intro j
  ext i
  change (A * (U.submatrix id Fin.castSucc)) i j = U i j.succ
  rw [UV]
  fin_cases i
  · exact A_V_row0 j
  · exact A_V_row1 j
  · exact A_V_row2 j
  · exact A_V_row3 j
  · exact A_V_row4 j
  · exact A_V_row5 j
  · exact A_V_row6 j
  · exact A_V_row7 j
  · exact A_V_row8 j
  · exact A_V_row9 j
  · exact A_V_row10 j
  · exact A_V_row11 j
  · exact A_V_row12 j
  · exact A_V_row13 j
  · exact A_V_row14 j
  · exact A_V_row15 j
  · exact A_V_row16 j
  · exact A_V_row17 j
  · exact A_V_row18 j
  · exact A_V_row19 j
lemma final : (fun i => U i (Fin.last 20)) + V.mulVec coeffs = 0 := by decide +kernel
lemma f_def : f = X ^ 20 + polyVec coeffs := by
  norm_num [f, poly, polyVec, coeffs, Fin.sum_univ_succ, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring
lemma charpoly_A : A.charpoly = f := by
  rw [f_def]
  exact charpoly_of_chain A V B U (Pi.single 0 1) coeffs (by decide +kernel) first_column step UV B_V final
lemma charpoly : N0Num.charpoly.map (Int.castRingHom (ZMod 131)) = f := by
  rw [← Matrix.charpoly_map, matrix_reduce, charpoly_A]
end P131
end ModularPencil

end

end OAI
