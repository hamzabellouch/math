import OAI.Combinatorics.ContingencyTables.Transport.WordContextVariance
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperExposureVariance
import OAI.Combinatorics.ContingencyTables.Transport.FiniteExposureBudget

namespace OAI

/-! # Global transversal variance for the literal first-paper profiles -/

namespace ContingencyTables.RowMajorEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport
open FirstPaperContextTransport FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem firstPaper_word_context_variance (r : I → ℕ) (c : J → ℕ)
    (k : Fin (Fintype.card (Cells (paperSmall r c))))
    (τ : Fin k.val → Fin ((dimensionAllowance (I := I) (J := J))^20+1))
    (H : SmallProfile (paperSmall r c) → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let small := paperSmall r c
    let B := paperCapacity small r d (d^12) U
    let w := wordWeight small B r c (d^12) U
    let G := wordObservable small U H
    let cw := fun j : Fin (U+1) => fibreWeight
      (fibreWeight w (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
    let σ := prefixExtension small (enumeration small k).val U (earlierWordChoices small U k τ)
    variance (fun j => ∑ a,cw j a) (fun j => mean (cw j) G) ≤
      4*d*((U:ℝ)+1)^6*
        physicalContextEnergy small B (enumeration small k).val σ (hardMarginal small B r c (d^12)) H := by
  dsimp only
  have hd : 2 ≤ dimensionAllowance (I := I) (J := J) := by unfold dimensionAllowance; omega
  have hU : 2 ≤ (dimensionAllowance (I := I) (J := J))^20 :=
    hd.trans (Nat.le_self_pow (by decide) _)
  have hv := word_context_variance (paperSmall r c)
    (paperCapacity (paperSmall r c) r (dimensionAllowance (I := I) (J := J))
      ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20))
    r c _ _ hU
    (fun i j hij => by simp only [paperCapacity,hij,ite_true])
    (fun i j hij => by simp only [paperCapacity,hij,Bool.false_eq_true,ite_false]; omega)
    (paper_residual_capacity r c _ _ _ dimension_le_allowance) k τ H
  dsimp only at hv
  refine hv.trans (mul_le_mul_of_nonneg_right
    (exposure_coefficient _ _ _ (by omega)
      (later_card_le_allowance _ _ (laterEnumeration (paperSmall r c) k))) ?_)
  exact physicalContextEnergy_nonnegative _ _ _ _ _ H (hardMarginal_nonnegative _ _ r c _)

lemma firstPaper_prefixContribution_le (r : I → ℕ) (c : J → ℕ)
    (k : Fin (Fintype.card (Cells (paperSmall r c))))
    (H : SmallProfile (paperSmall r c) → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let small := paperSmall r c
    let B := paperCapacity small r d (d^12) U
    prefixContribution (wordWeight small B r c (d^12) U) (wordObservable small U H) k ≤
      4*d*((U:ℝ)+1)^6*physicalEnergy small B (hardMarginal small B r c (d^12)) H := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let small := paperSmall r c
  let B := paperCapacity small r d (d^12) U
  let K : ℝ := 4*d*((U:ℝ)+1)^6
  let E := fun τ : Earlier small (enumeration small k).val → Fin (U+1) =>
    physicalContextEnergy small B (enumeration small k).val
      (prefixExtension small (enumeration small k).val U τ) (hardMarginal small B r c (d^12)) H
  have hs : (∑ τ : Fin k.val → Fin (U+1),E (earlierWordChoices small U k τ))=∑ τ,E τ := by
    apply Fintype.sum_equiv (earlierWordChoices small U k)
    intro τ
    rfl
  calc
    _ ≤ ∑ τ : Fin k.val → Fin (U+1),K*E (earlierWordChoices small U k τ) := by
      unfold prefixContribution partitionContribution
      apply Finset.sum_le_sum
      intro τ _
      exact firstPaper_word_context_variance r c k τ H
    _ = K*∑ τ,E τ := by rw [← Finset.mul_sum,hs]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_physicalContextEnergy_le small B (enumeration small k).val U
        (fun i j hij => by simp only [B,paperCapacity,hij,ite_true])
        (hardMarginal small B r c (d^12)) H (hardMarginal_nonnegative _ _ _ _ _)) (by positivity)

/-- Actual first-paper balanced choices, weighted by every physical
large completion, satisfy the paper's global transversal variance bound. -/
theorem firstPaper_transversal_variance (r : I → ℕ) (c : J → ℕ)
    (H : SmallProfile (paperSmall r c) → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let small := paperSmall r c
    let B := paperCapacity small r d (d^12) U
    variance (wordWeight small B r c (d^12) U) (wordObservable small U H) ≤
      4*(d:ℝ)^2*((U:ℝ)+1)^6*physicalEnergy small B (hardMarginal small B r c (d^12)) H := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let small := paperSmall r c
  let B := paperCapacity small r d (d^12) U
  let E := physicalEnergy small B (hardMarginal small B r c (d^12)) H
  have hq : Fintype.card (Cells small) ≤ d := (small_card_le_dimension small).trans dimension_le_allowance
  have hE : 0 ≤ E := graphEnergy_nonnegative (vertices small B) (hardMarginal small B r c (d^12)) H
    (hardMarginal_nonnegative small B r c (d^12))
  exact variance_le_polynomial_budget (wordWeight small B r c (d^12) U) (wordObservable small U H)
    (fun a => hardMarginal_nonnegative _ _ _ _ _ _) d U hq E hE
    (fun k => firstPaper_prefixContribution_le r c k H)

end ContingencyTables.RowMajorEnumeration

end OAI
