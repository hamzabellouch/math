import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementGeometryBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeCounts
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryUnnormalizedFlagError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryUnnormalizedFlagError
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistorySymbolicEncoding
open HistorySelectedPairDerivativeCounts HistoryBulkReplacementGeometry

def coordinateGrowth (k : ℕ) : ℝ := 2*(countCoefficient k:ℝ)*(bulkScale k+1)

lemma coordinateGrowth_pos (k : ℕ) : 0 < coordinateGrowth k := by
  have hc : 0 < (countCoefficient k:ℝ) := by exact_mod_cast countCoefficient_pos k
  have hs : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  unfold coordinateGrowth
  positivity

theorem selected_pairKey_card_le {L : ℝ} (hL : 0 ≤ L) {k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) h)
    (hg : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) g) (hl : l ≤ k) :
    (Fintype.card (PairKey h g):ℝ) ≤ coordinateGrowth k*(L+1) := by
  have hc : (Fintype.card (PairKey h g):ℝ) ≤
      2*(countCoefficient k:ℝ)*((bulkSize k L/2:ℕ)+1) := by
    exact_mod_cast pairKey_card_le hh hg hl
  have hb : ((bulkSize k L/2:ℕ):ℝ) ≤ bulkSize k L := by exact_mod_cast Nat.div_le_self (bulkSize k L) 2
  have hm := (bulkSize_bounds k hL).2
  have hs : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  calc
    _ ≤ 2*(countCoefficient k:ℝ)*((bulkSize k L/2:ℕ)+1) := hc
    _ ≤ 2*(countCoefficient k:ℝ)*((bulkScale k+1)*(L+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = _ := by unfold coordinateGrowth; ring

def spectatorCost (k : ℕ) (C : ℝ) : ℝ :=
  ((2:ℝ)^(k+1)+|C|+1)*(bulkScale k+1)

lemma spectatorCost_pos (k : ℕ) (C : ℝ) : 0 < spectatorCost k C := by
  have hs : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  unfold spectatorCost
  positivity

theorem spectator_prefactor_le {k l : ℕ} (hl : l ≤ k) {L : ℝ} (hL : 0 ≤ L)
    (C : ℝ) (outside : List ℕ) (hpos : ∀p∈outside,0 < p)
    (hlen : outside.length ≤ bulkSize k L)
    (hlog : ∀p∈outside, Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) :
    (outside.prod:ℝ)^(2^(l+1))*Real.exp (C*((bulkSize k L:ℝ)+1)) ≤
      Real.exp (commonLogBudget (spectatorCost k C) L) := by
  have hp : 0 < (outside.prod:ℝ) := by exact_mod_cast List.prod_pos hpos
  have hh := log_nat_product_le outside (Real.exp ((1/1000:ℝ)*L)) hpos hlog
  have hlen' : (outside.length:ℝ) ≤ bulkSize k L := by exact_mod_cast hlen
  have hlog' := hh.trans (mul_le_mul_of_nonneg_right hlen' (Real.exp_nonneg _))
  have hexp : Real.exp ((1/1000:ℝ)*L) ≤ Real.exp ((11/10000:ℝ)*L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpow : ((2^(l+1):ℕ):ℝ) ≤ (2:ℝ)^(k+1) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) (Nat.add_le_add_right hl 1)
  have hcount := (bulkSize_bounds k hL).2
  have hs : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  have hm : (bulkSize k L:ℝ) ≤ (bulkScale k+1)*(L+1) := by nlinarith
  have hm1 : (bulkSize k L:ℝ)+1 ≤ (bulkScale k+1)*(L+1) := by nlinarith
  have he1 : 1 ≤ Real.exp ((11/10000:ℝ)*L) := Real.one_le_exp (by positivity)
  have hpiece := mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg (2^(l+1)) (α:=ℝ))
  have hpiece' := mul_le_mul hpow (mul_le_mul hm hexp (Real.exp_nonneg _) (by positivity))
    (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)) (by positivity : 0 ≤ (2:ℝ)^(k+1))
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C)
    (by positivity : 0 ≤ (bulkSize k L:ℝ)+1)
  have hC' := mul_le_mul_of_nonneg_left hm1 (abs_nonneg C)
  have hC'' := le_mul_of_one_le_right
    (by positivity : 0 ≤ |C| * ((bulkScale k+1)*(L+1))) he1
  have hlin : (L+1) ≤ (L+1)^2 := by nlinarith
  have hbudget := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlin (spectatorCost_pos k C).le)
    (Real.exp_nonneg ((11/10000:ℝ)*L))
  calc
    _ = Real.exp (((2^(l+1):ℕ):ℝ)*Real.log (outside.prod:ℝ)+C*((bulkSize k L:ℝ)+1)) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hp]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold commonLogBudget
      unfold spectatorCost at hbudget ⊢
      have hz : 0 ≤ (bulkScale k+1)*(L+1)*Real.exp ((11/10000:ℝ)*L) := by positivity
      nlinarith

end Ostmann.Arithmetic.HistoryUnnormalizedFlagError

end

end OAI
