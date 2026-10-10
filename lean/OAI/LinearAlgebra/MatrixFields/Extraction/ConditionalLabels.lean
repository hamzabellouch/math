import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.ZeroLeafRates

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation.StageHierarchyResources

open Filter HierarchySeparationRates LabelHierarchyCounts
open scoped BigOperators Topology

universe u v

local instance (priority := low) {B : Type*} : DecidableEq B := Classical.decEq B

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

def stageRefinementCount (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) : ℕ :=
  refinementCount (sourcePrefixCounts (fun a => t * counts a) labels) n

def stageNodeCounts (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ)
    (r : LabelRecord Label n) (s : Label n) : ℕ :=
  sourcePrefixCounts counts labels (n + 1) (r, s)

theorem stageRefinementCount_eq_nodeProduct (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n t : ℕ) :
    stageRefinementCount counts labels n t = pairingProduct (stageNodeCounts counts labels n) t := by
  unfold stageRefinementCount refinementCount pairingProduct
  apply Finset.prod_congr rfl
  intro r hr
  change Nat.multinomial Finset.univ
      (fun s : Label n => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s)) =
    Nat.multinomial Finset.univ
      (fun s : Label n => t * sourcePrefixCounts counts labels (n + 1) (r, s))
  apply Nat.multinomial_congr
  intro s hs
  exact sourcePrefixCounts_mul counts labels t (n + 1) (r, s)

theorem stageRefinementCount_eq_sourcePoolProduct (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ) (n : Fin depth) (t : ℕ) :
    stageRefinementCount counts labels n.val t =
      ∏ r : LabelRecord Label n.val,
        poolTypeCount (sourcePoolCounts counts labels depth) ⟨n, r⟩ t :=
  stageRefinementCount_eq_nodeProduct counts labels n.val t

theorem stageRefinementCount_pos (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) : 0 < stageRefinementCount counts labels n t := by
  unfold stageRefinementCount refinementCount
  exact Finset.prod_pos (fun r _ => Nat.multinomial_pos _ _)

theorem stageConditionalWords_card {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    Fintype.card (ConditionalWords w
      (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))) =
      stageRefinementCount counts labels n t := by
  exact conditionalWords_card w
    (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))
    (fun r => (hword r).trans
      (sourcePrefixCounts_compatible (fun a => t * counts a) labels n r))

theorem stageConditionalPool_card {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    (Finset.univ.filter (fun fine : Position → Label n =>
      ∀ r s, Fintype.card {i // w i = r ∧ fine i = s} =
        sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))).card =
      stageRefinementCount counts labels n t := by
  simpa only [ConditionalWords, Fintype.card_subtype] using
    stageConditionalWords_card counts labels n t w hword

theorem stageConditionalWords_nonempty {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    Nonempty (ConditionalWords w
      (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))) := by
  apply Fintype.card_pos_iff.mp
  rw [stageConditionalWords_card counts labels n t w hword]
  exact stageRefinementCount_pos counts labels n t

def stageEntropyRate (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ) : ℝ :=
  poolEntropyTotal (stageNodeCounts counts labels n)

theorem stageEntropyRate_nonneg (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n : ℕ) : 0 ≤ stageEntropyRate counts labels n := by
  exact Finset.sum_nonneg (fun r _ => populationEntropyRate_nonneg
    (stageNodeCounts counts labels n r))

theorem tendsto_log_stageRefinementCount_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log (stageRefinementCount counts labels n t : ℝ) / (t : ℝ))
      atTop (𝓝 (stageEntropyRate counts labels n)) := by
  simpa only [stageRefinementCount_eq_nodeProduct, stageEntropyRate] using
    tendsto_log_pairingProduct_div (stageNodeCounts counts labels n)

def stageCost (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ) : ℕ :=
  LabelHierarchySeparation.poolAuxiliaryCost (stageRefinementCount counts labels n t)

theorem tendsto_log_stageCost_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log (stageCost counts labels n t : ℝ) / (t : ℝ))
      atTop (𝓝 (stageEntropyRate counts labels n)) :=
  LabelHierarchySeparation.tendsto_log_poolAuxiliaryCost_div_nat
    (stageRefinementCount_pos counts labels n) (stageEntropyRate_nonneg counts labels n)
    (tendsto_log_stageRefinementCount_div counts labels n)

def stagePairingProduct (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) : ℕ :=
  ∏ n : Fin depth, stageRefinementCount counts labels n.val t

def stageAuxiliaryBudget (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) : ℕ :=
  ∏ n : Fin depth, stageCost counts labels n.val t

theorem stagePairingProduct_succ (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) :
    stagePairingProduct counts labels (n + 1) t =
      stagePairingProduct counts labels n t * stageRefinementCount counts labels n t := by
  exact Fin.prod_univ_castSucc
    (fun i : Fin (n + 1) => stageRefinementCount counts labels i.val t)

theorem stageAuxiliaryBudget_succ (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) :
    stageAuxiliaryBudget counts labels (n + 1) t =
      stageAuxiliaryBudget counts labels n t * stageCost counts labels n t := by
  exact Fin.prod_univ_castSucc
    (fun i : Fin (n + 1) => stageCost counts labels i.val t)

theorem stagePairingProduct_eq_exactWords_card (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    stagePairingProduct counts labels depth t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  unfold stagePairingProduct stageRefinementCount
  rw [Fin.prod_univ_eq_prod_range]
  exact source_refinementCount_product_eq_exactWords_card
    (fun a => t * counts a) labels depth hinjective

theorem stagePairingProduct_le_budget (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    stagePairingProduct counts labels depth t ≤ stageAuxiliaryBudget counts labels depth t := by
  exact Finset.prod_le_prod (fun n _ =>
    LabelHierarchySeparation.population_le_poolAuxiliaryCost
      (stageRefinementCount counts labels n.val t))

theorem stageAuxiliaryBudget_pos (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    0 < stageAuxiliaryBudget counts labels depth t := by
  exact Finset.prod_pos (fun n _ => LabelHierarchySeparation.poolAuxiliaryCost_pos
    (stageRefinementCount counts labels n.val t))

abbrev StageAuxiliaryCoordinates (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) :=
  ∀ n : Fin depth,
    LabelHierarchySeparation.PoolAuxiliaryGroup (stageRefinementCount counts labels n.val t)

local instance stageHierarchyAuxiliaryModulusNeZero (population : ℕ) :
    NeZero (4 * Separation.gridWidth population) :=
  ⟨Nat.ne_of_gt (Nat.mul_pos (by decide)
    (lt_of_lt_of_le (by decide : 0 < 2)
      (Separation.gridWidth_ge_two population)))⟩

def stageAuxiliaryTensor (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) :
    Tensor ℂ (StageAuxiliaryCoordinates counts labels depth t)
      (StageAuxiliaryCoordinates counts labels depth t) (StageAuxiliaryCoordinates counts labels depth t) :=
  LabelHierarchySeparation.bankTensor (fun n : Fin depth =>
    LabelHierarchySeparation.poolAuxiliaryTensor (stageRefinementCount counts labels n.val t))

theorem stageAuxiliaryTensor_rankAtMost (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    Tensor.RankAtMost (stageAuxiliaryTensor counts labels depth t)
      (stageAuxiliaryBudget counts labels depth t) := by
  exact LabelHierarchySeparation.bankTensor_rankAtMost
    (fun n : Fin depth => LabelHierarchySeparation.poolAuxiliaryTensor
      (stageRefinementCount counts labels n.val t))
    (fun n => stageCost counts labels n.val t)
    (fun n => LabelHierarchySeparation.poolAuxiliaryTensor_rankAtMost
      (stageRefinementCount counts labels n.val t))

theorem stageAuxiliaryTensor_borderRankAtMost (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    Tensor.BorderRankAtMost (stageAuxiliaryTensor counts labels depth t)
      (stageAuxiliaryBudget counts labels depth t) :=
  (stageAuxiliaryTensor_rankAtMost counts labels depth t).borderRankAtMost

abbrev StagePairingCoordinates (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) := ∀ n : Fin depth, Fin (stageRefinementCount counts labels n.val t)

theorem card_stagePairingCoordinates (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    Fintype.card (StagePairingCoordinates counts labels depth t) =
      stagePairingProduct counts labels depth t := by
  simp only [StagePairingCoordinates, Fintype.card_pi, Fintype.card_fin, stagePairingProduct]

theorem sum_stageEntropyRate_eq_nodeEntropyTotal (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ) :
    (∑ n : Fin depth, stageEntropyRate counts labels n.val) =
      poolEntropyTotal (sourcePoolCounts counts labels depth) := by
  simp only [stageEntropyRate, poolEntropyTotal, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  rfl

theorem sum_stageEntropyRate_eq_source (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∑ n : Fin depth, stageEntropyRate counts labels n.val) = populationEntropyRate counts := by
  rw [sum_stageEntropyRate_eq_nodeEntropyTotal]
  exact source_poolEntropyTotal_eq counts labels depth hinjective

theorem tendsto_log_stageAuxiliaryBudget_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts)) := by
  have h := Separation.tendsto_log_nat_prod_div_nat (I := Fin depth) Finset.univ
    (fun n _ t => LabelHierarchySeparation.poolAuxiliaryCost_pos
      (stageRefinementCount counts labels n.val t))
    (fun n _ => tendsto_log_stageCost_div counts labels n.val)
  simpa only [stageAuxiliaryBudget, stageCost,
    sum_stageEntropyRate_eq_source counts labels depth hinjective] using h

theorem tendsto_log_stagePairingProduct (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (stagePairingProduct counts labels depth t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [stagePairingProduct_eq_exactWords_card counts labels depth hinjective] using
    tendsto_log_exactWords_card_mul counts hD

theorem tendsto_log_stageAuxiliaryBudget (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hmain : populationEntropyRate counts / (∑ a, counts a : ℕ) =
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    unfold populationEntropyRate
    exact mul_div_cancel_left₀ _ hD'
  simpa only [div_div, hmain] using
    (tendsto_log_stageAuxiliaryBudget_div counts labels depth hinjective).div_const
      ((∑ a, counts a : ℕ) : ℝ)

theorem source_stage_resource_rates (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∀ t, Tensor.RankAtMost (stageAuxiliaryTensor counts labels depth t)
      (stageAuxiliaryBudget counts labels depth t)) ∧
      (∀ t, stagePairingProduct counts labels depth t =
        Fintype.card (ExactWords (fun a => t * counts a))) ∧
      (∀ t, stagePairingProduct counts labels depth t ≤ stageAuxiliaryBudget counts labels depth t) ∧
      Tendsto
        (fun t : ℕ => Real.log (stagePairingProduct counts labels depth t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) ∧
      Tendsto
        (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) :=
  ⟨stageAuxiliaryTensor_rankAtMost counts labels depth,
    stagePairingProduct_eq_exactWords_card counts labels depth hinjective,
    stagePairingProduct_le_budget counts labels depth,
    tendsto_log_stagePairingProduct counts hD labels depth hinjective,
    tendsto_log_stageAuxiliaryBudget counts hD labels depth hinjective⟩

end MatrixMultiplication.Foundation.StageHierarchyResources

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation Filter
open scoped Topology BigOperators Classical

inductive ReaderPair where
  | xy | xz | yz
  deriving DecidableEq

instance : Fintype ReaderPair where
  elems := {.xy, .xz, .yz}
  complete pair := by cases pair <;> simp

namespace ConditionalLabels

universe u v

section PairAccounting

variable {I : Type u} [Fintype I]

def pairingSize (population : I → ℕ) (reader : I → ReaderPair)
    (pair : ReaderPair) : ℕ :=
  ∏ i, if reader i = pair then population i else 1

def pairingRate (rate : I → ℝ) (reader : I → ReaderPair)
    (pair : ReaderPair) : ℝ :=
  ∑ i, if reader i = pair then rate i else 0

theorem pairingSize_pos (population : I → ℕ) (reader : I → ReaderPair)
    (pair : ReaderPair) (positive : ∀ i, 0 < population i) :
    0 < pairingSize population reader pair := by
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact positive i
  · exact Nat.zero_lt_one

theorem pairingRate_nonneg (rate : I → ℝ) (reader : I → ReaderPair)
    (pair : ReaderPair) (nonneg : ∀ i, 0 ≤ rate i) :
    0 ≤ pairingRate rate reader pair := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact nonneg i
  · exact le_rfl

theorem pairingSize_product (population : I → ℕ) (reader : I → ReaderPair) :
    pairingSize population reader .xy * pairingSize population reader .xz *
      pairingSize population reader .yz = ∏ i, population i := by
  simp only [pairingSize, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases reader i <;> simp

theorem pairingRate_sum (rate : I → ℝ) (reader : I → ReaderPair) :
    pairingRate rate reader .xy + pairingRate rate reader .xz +
      pairingRate rate reader .yz = ∑ i, rate i := by
  simp only [pairingRate, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases reader i <;> simp

theorem tendsto_log_pairingSize (population : I → ℕ → ℕ)
    (rate : I → ℝ) (reader : I → ReaderPair) (pair : ReaderPair)
    (positive : ∀ i n, 0 < population i n)
    (growth : ∀ i, Tendsto (fun n => Real.log (population i n : ℝ) / (n : ℝ))
      atTop (𝓝 (rate i))) :
    Tendsto (fun n => Real.log (pairingSize (fun i => population i n) reader pair : ℝ) /
      (n : ℝ)) atTop (𝓝 (pairingRate rate reader pair)) := by
  apply Separation.tendsto_log_nat_prod_div_nat Finset.univ
  · intro i _ n
    split_ifs
    · exact positive i n
    · exact Nat.zero_lt_one
  · intro i _
    by_cases h : reader i = pair
    · simpa only [h, ite_true] using growth i
    · simpa only [h, ite_false, Nat.cast_one, Real.log_one, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end PairAccounting

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

open StageHierarchyResources HierarchySeparationRates

def stagePairingSize (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) (t : ℕ) : ℕ :=
  pairingSize (fun n : Fin depth => stageRefinementCount counts labels n.val t) reader pair

def stagePairingRate (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) : ℝ :=
  pairingRate (fun n : Fin depth => stageEntropyRate counts labels n.val) reader pair

theorem stagePairingSize_product (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    stagePairingSize counts labels depth reader .xy t *
      stagePairingSize counts labels depth reader .xz t *
      stagePairingSize counts labels depth reader .yz t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [stagePairingSize, stagePairingSize, stagePairingSize, pairingSize_product]
  exact stagePairingProduct_eq_exactWords_card counts labels depth complete t

theorem stagePairingRate_sum (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    stagePairingRate counts labels depth reader .xy +
      stagePairingRate counts labels depth reader .xz +
      stagePairingRate counts labels depth reader .yz = populationEntropyRate counts := by
  rw [stagePairingRate, stagePairingRate, stagePairingRate, pairingRate_sum]
  exact sum_stageEntropyRate_eq_source counts labels depth complete

theorem tendsto_log_stagePairingSize (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      (t : ℝ)) atTop (𝓝 (stagePairingRate counts labels depth reader pair)) := by
  exact tendsto_log_pairingSize _ _ reader pair
    (fun n => stageRefinementCount_pos counts labels n.val)
    (fun n => tendsto_log_stageRefinementCount_div counts labels n.val)

theorem tendsto_log_stagePairingSize_normalized (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (stagePairingRate counts labels depth reader pair / (∑ a, counts a : ℕ))) := by
  simpa only [div_div] using
    (tendsto_log_stagePairingSize counts labels depth reader pair).div_const
      ((∑ a, counts a : ℕ) : ℝ)

theorem auxiliary_overhead_tendsto_zero (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    Tendsto (fun t =>
      (Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
        Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ)) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 0) := by
  have h := (tendsto_log_stageAuxiliaryBudget counts hD labels depth complete).sub
    (tendsto_log_exactWords_card_mul counts hD)
  simpa only [sub_self, sub_div] using h

theorem auxiliary_overhead_nonneg (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    0 ≤ Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
      Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) := by
  apply sub_nonneg.mpr
  rw [← stagePairingProduct_eq_exactWords_card counts labels depth complete t]
  apply Real.log_le_log
  · apply Nat.cast_pos.mpr
    exact Finset.prod_pos (fun n _ => stageRefinementCount_pos counts labels n.val t)
  · exact_mod_cast stagePairingProduct_le_budget counts labels depth t

theorem charged_cost_tendsto (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) (C : ℝ) :
    Tendsto (fun t => C +
      (Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
        Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ)) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 C) := by
  simpa only [add_zero] using
    (auxiliary_overhead_tendsto_zero counts hD labels depth complete).const_add C

theorem limit_le_source_cost (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth))
    {value : ℕ → ℝ} {rate C : ℝ}
    (limit : Tendsto value atTop (𝓝 rate))
    (finite_bound : ∀ᶠ t in atTop, value t ≤ C +
      (Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
        Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ)) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) : rate ≤ C :=
  le_of_tendsto_of_tendsto limit
    (charged_cost_tendsto counts hD labels depth complete C) finite_bound

def lawPairingRate (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) : ℝ :=
  pairingRate (fun n : Fin depth =>
    (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n.val) reader pair

theorem lawPairingRate_sum (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz +
      lawPairingRate p labels depth reader .yz = finiteEntropy p.mass := by
  rw [lawPairingRate, lawPairingRate, lawPairingRate, pairingRate_sum,
    Fin.sum_univ_eq_sum_range]
  exact FiniteLabelHierarchy.ofLawLabels_refinementEntropy_sum p labels depth complete

theorem incident_rate_eq_prefix_entropy (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth cut : ℕ) (hcut : cut ≤ depth)
    (reader : Fin depth → ReaderPair)
    (incident_prefix : ∀ n : Fin depth,
      (reader n = .xy ∨ reader n = .xz) ↔ n.val < cut) :
    lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz =
      finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
  let hierarchy := FiniteLabelHierarchy.ofLawLabels p labels depth
  have hterms : ∀ n : Fin depth,
      (if reader n = .xy then hierarchy.refinementEntropy n.val else 0) +
        (if reader n = .xz then hierarchy.refinementEntropy n.val else 0) =
        if n.val < cut then hierarchy.refinementEntropy n.val else 0 := by
    intro n
    cases hr : reader n with
    | xy =>
        have hn := (incident_prefix n).mp (Or.inl hr)
        simp [hn]
    | xz =>
        have hn := (incident_prefix n).mp (Or.inr hr)
        simp [hn]
    | yz =>
        have hn : ¬n.val < cut := by
          intro h
          rcases (incident_prefix n).mpr h with h | h <;> simp [hr] at h
        simp [hn]
  have hfilter : (Finset.range depth).filter (fun n => n < cut) = Finset.range cut := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    lawPairingRate p labels depth reader .xy +
        lawPairingRate p labels depth reader .xz =
        ∑ n : Fin depth, if n.val < cut then hierarchy.refinementEntropy n.val else 0 := by
      simp only [lawPairingRate, pairingRate, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun n _ => hterms n)
    _ = ∑ n ∈ Finset.range cut, hierarchy.refinementEntropy n := by
      rw [show (∑ n : Fin depth, if n.val < cut then hierarchy.refinementEntropy n.val else 0) =
        ∑ n ∈ Finset.range depth, if n < cut then hierarchy.refinementEntropy n else 0 from
          Fin.sum_univ_eq_sum_range
            (fun n => if n < cut then hierarchy.refinementEntropy n else 0) depth]
      rw [← Finset.sum_filter, hfilter]
    _ = finiteEntropy (hierarchy.prefixLaw cut hcut).mass :=
      (hierarchy.prefixLaw_entropy cut hcut).symm
    _ = finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
      rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass]

theorem remaining_rate_eq_entropy_sub_prefix (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth cut : ℕ) (hcut : cut ≤ depth)
    (reader : Fin depth → ReaderPair)
    (incident_prefix : ∀ n : Fin depth,
      (reader n = .xy ∨ reader n = .xz) ↔ n.val < cut)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    lawPairingRate p labels depth reader .yz = finiteEntropy p.mass -
      finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
  have hsum := lawPairingRate_sum p labels depth reader complete
  have hprefix := incident_rate_eq_prefix_entropy p labels depth cut hcut reader incident_prefix
  linarith

end SourceHierarchy
end ConditionalLabels
end MatrixMultiplication

end
end

end MatrixAllFields

end OAI
