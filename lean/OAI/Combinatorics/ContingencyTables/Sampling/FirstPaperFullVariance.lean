import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalRepairGraph
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperTransversalVariance
import OAI.Combinatorics.ContingencyTables.Transport.FiniteGraphPoincareBudget

namespace OAI

/-! # The source Poincare bound for the full literal physical small graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The literal physical encoding consists of the balanced transversal
words and the positive single-defect profiles. Zero-weight transversal
words may be retained; they contribute zero to both variance and energy. -/
theorem firstPaper_full_variance (r : I → ℕ) (c : J → ℕ)
    (H : SmallProfile (paperSmall r c) → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let L := d^12
    let small := paperSmall r c
    let B := paperCapacity small r d L U
    let hB := fun i j (hij : small i j=true) => show B i j=U by simp only [B,paperCapacity,hij,ite_true]
    let w := wordWeight small B r c L U
    let v := fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val)
    let G := wordObservable small U H
    let K := fun z : PositiveDefects small B r c L => H (naturalProfile z.val)
    variance (Sum.elim w v) (Sum.elim G K) ≤ 770*(d:ℝ)^4*(U:ℝ)^6*fullEnergy r c U L B hB H := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let L := d^12
  let small := paperSmall r c
  let B := paperCapacity small r d L U
  have hB : ∀ i j,small i j=true → B i j=U := fun i j hij => by simp only [B,paperCapacity,hij,ite_true]
  have hcap : ∀ T : ResidualTables small r c (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L),∀ i j,T.val.val i j ≤ B i j :=
    paper_residual_capacity r c d L U dimension_le_allowance
  let E := fullEnergy r c U L B hB H
  have hE : 0 ≤ E := fullEnergy_nonnegative r c U L B hB H
  have hd : 1 ≤ d := by dsimp only [d]; unfold dimensionAllowance; omega
  have hU : 1 ≤ U := hd.trans (Nat.le_self_pow (by decide) _)
  have hq : Fintype.card (Cells small) ≤ d := (small_card_le_dimension small).trans dimension_le_allowance
  have hT : Fintype.card (Cells small×Cells small) ≤ d^2 := by
    simpa only [Fintype.card_prod,pow_two] using Nat.mul_le_mul hq hq
  have hvar : variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      4*(d:ℝ)^2*((U:ℝ)+1)^6*E := by
    exact (firstPaper_transversal_variance r c H).trans
      (mul_le_mul_of_nonneg_left (physicalEnergy_le_full r c U L B hB H) (by positivity))
  exact variance_repaired_graph_budget (wordWeight small B r c L U)
    (fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val))
    (wordObservable small U H) (fun z => H (naturalProfile z.val))
    (repairWord r c U L B hB) (defectLabels small B r c L)
    (fun a => hardMarginal_nonnegative _ _ _ _ _ _) (fun z => le_of_lt z.property.2)
    (repairWord_weight r c U L B hB hcap) (repairWord_type_injective r c U L B hB)
    d U hd hU hT E hE hvar (actual_repair_energy_le r c U L B hB hcap H)

end ContingencyTables.SmallGraphProfiles

end OAI
