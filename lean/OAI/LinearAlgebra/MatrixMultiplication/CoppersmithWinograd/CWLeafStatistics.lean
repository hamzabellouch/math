import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWLeafRestrictions
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Basic

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

namespace MatrixMultiplication.CWLeafStatistics

open MatrixMultiplication.Foundation

def weight (x : Fin 7) : ℕ := if x.val = 0 then 0 else if x.val = 6 then 2 else 1

def pairStatistic (x : Fin 7 × Fin 7) : Fin 6 :=
  if weight x.1 + weight x.2 = 0 then 0
  else if weight x.1 + weight x.2 = 1 then 1
  else if weight x.1 + weight x.2 = 2 then
    if weight x.1 = 1 ∧ weight x.2 = 1 then 2 else 3
  else if weight x.1 + weight x.2 = 3 then 4 else 5

theorem statistic_weight : ∀ x : Fin 7 × Fin 7,
    AllFieldParameters.statisticWeight (pairStatistic x) = weight x.1 + weight x.2 := by
  decide +kernel

theorem pair_multiplicity : ∀ i : Fin 6,
    Fintype.card {x : Fin 7 × Fin 7 // pairStatistic x = i} =
      AllFieldParameters.multiplicity i := by
  decide +kernel

theorem complement_weight : ∀ x : Fin 7,
    weight (CWLeafRestrictions.complement 5 x) + weight x = 2 := by
  decide +kernel

theorem complement_statistic : ∀ x : Fin 7 × Fin 7,
    pairStatistic (CWLeafRestrictions.complement 5 x.1,
      CWLeafRestrictions.complement 5 x.2) =
      AllFieldParameters.kappa (pairStatistic x) := by
  decide +kernel

theorem ordered_pair_multiplicity (i j : Fin 6) :
    Fintype.card {x : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
      pairStatistic x.1 = i ∧ pairStatistic x.2 = j} =
      AllFieldParameters.multiplicity i * AllFieldParameters.multiplicity j := by
  let e : {x : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
      pairStatistic x.1 = i ∧ pairStatistic x.2 = j} ≃
      {x : Fin 7 × Fin 7 // pairStatistic x = i} ×
        {x : Fin 7 × Fin 7 // pairStatistic x = j} :=
    { toFun := fun x => (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
      invFun := fun x => ⟨(x.1.val, x.2.val), x.1.property, x.2.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, pair_multiplicity, pair_multiplicity]

end MatrixMultiplication.CWLeafStatistics

end OAI
