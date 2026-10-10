import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWWindowedLeaves

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWCompleteStatistics

open CWWindowedLeaves CWLeafStatistics CWStrands AllFieldParameters
open scoped BigOperators

attribute [local instance] Classical.propDecidable

def pairEquiv : Raw 2 ≃ (Fin 7 × Fin 7) where
  toFun w := (w 0, w 1)
  invFun u := ![u.1, u.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv u := by cases u; rfl

def orderedEquiv : Raw 4 ≃ ((Fin 7 × Fin 7) × (Fin 7 × Fin 7)) where
  toFun w := ((w 0, w 1), (w 2, w 3))
  invFun u := ![u.1.1, u.1.2, u.2.1, u.2.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv u := by cases u with | mk u v => cases u; cases v; rfl

def twoStatistic (w : Raw 2) : Fin 6 := pairStatistic (pairEquiv w)
def fourStatistic (w : Raw 4) : Fin 6 × Fin 6 :=
  (pairStatistic (orderedEquiv w).1, pairStatistic (orderedEquiv w).2)

def complementStatistic : Fin 6 ≃ Fin 6 :=
  { toFun := kappa
    invFun := kappa
    left_inv := kappa_involution
    right_inv := kappa_involution }

def orderedComplementStatistic : (Fin 6 × Fin 6) ≃ (Fin 6 × Fin 6) :=
  Equiv.prodCongr complementStatistic complementStatistic

theorem two_weight (w : Raw 2) :
    CWStrands.weight w = statisticWeight (twoStatistic w) := by
  rw [twoStatistic, statistic_weight]
  simp [CWStrands.weight, pairEquiv, Fin.sum_univ_succ]

theorem four_weight (w : Raw 4) :
    CWStrands.weight w = statisticWeight (fourStatistic w).1 +
      statisticWeight (fourStatistic w).2 := by
  simp only [fourStatistic, statistic_weight]
  simp [CWStrands.weight, orderedEquiv, Fin.sum_univ_succ, Nat.add_assoc]

theorem two_multiplicity (s : Fin 6) :
    Fintype.card {w : Raw 2 // twoStatistic w = s} = AllFieldParameters.multiplicity s := by
  let e : {w : Raw 2 // twoStatistic w = s} ≃
      {u : Fin 7 × Fin 7 // pairStatistic u = s} :=
    { toFun := fun w => ⟨pairEquiv w.val, w.property⟩
      invFun := fun u => ⟨pairEquiv.symm u.val, by simpa [twoStatistic] using u.property⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro u; apply Subtype.ext; simp }
  rw [Fintype.card_congr e, pair_multiplicity]

theorem four_multiplicity (s : Fin 6 × Fin 6) :
    Fintype.card {w : Raw 4 // fourStatistic w = s} =
      AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 := by
  let e : {w : Raw 4 // fourStatistic w = s} ≃
      {u : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
        pairStatistic u.1 = s.1 ∧ pairStatistic u.2 = s.2} :=
    { toFun := fun w => ⟨orderedEquiv w.val,
        congrArg Prod.fst w.property, congrArg Prod.snd w.property⟩
      invFun := fun u => ⟨orderedEquiv.symm u.val, by
        apply Prod.ext
        · simpa [fourStatistic] using u.property.1
        · simpa [fourStatistic] using u.property.2⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro u; apply Subtype.ext; simp }
  rw [Fintype.card_congr e, ordered_pair_multiplicity]

theorem two_complement (w : Raw 2) :
    twoStatistic (complementWord w) = complementStatistic (twoStatistic w) := by
  exact complement_statistic (pairEquiv w)

theorem four_complement (w : Raw 4) :
    fourStatistic (complementWord w) = orderedComplementStatistic (fourStatistic w) := by
  apply Prod.ext
  · exact complement_statistic (orderedEquiv w).1
  · exact complement_statistic (orderedEquiv w).2

theorem two_fixedWeight_multiplicity (a : ℕ) (s : Fin 6) (hs : statisticWeight s = a) :
    Fintype.card {w : Alphabet 2 a // twoStatistic w.val = s} =
      AllFieldParameters.multiplicity s := by
  rw [ExactStatisticWords.card_fixedWeight_fiber twoStatistic CWStrands.weight
    statisticWeight two_weight a s hs, two_multiplicity]

theorem four_fixedWeight_multiplicity (a : ℕ) (s : Fin 6 × Fin 6)
    (hs : statisticWeight s.1 + statisticWeight s.2 = a) :
    Fintype.card {w : Alphabet 4 a // fourStatistic w.val = s} =
      AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 := by
  rw [ExactStatisticWords.card_fixedWeight_fiber fourStatistic CWStrands.weight
    (fun s => statisticWeight s.1 + statisticWeight s.2) four_weight a s hs,
    four_multiplicity]

end MatrixMultiplication.CWCompleteStatistics

end

end OAI
