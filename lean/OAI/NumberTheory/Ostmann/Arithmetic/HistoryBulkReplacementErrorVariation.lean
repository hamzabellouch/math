import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementErrorBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReplacementError
open Construction Conclusion HistoryBulkPriorGrid PrimeCellReplacement PrimeProgression
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget LogCellPartition Filter
open scoped BigOperators

def modulusGrowthCost (k : ℕ) : ℝ := (2:ℝ)^k+2+residueCostExponent k

theorem all_modulus_power_growth_le (k : ℕ) {n a M : ℕ} {L : ℝ}
    (hn : n ≤ 2^k*bulkSize k L+2) (ha : a ≤ residueCostExponent k) (hM : 0 < M)
    (hmod : Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L)) :
    (M:ℝ)^(n+a) ≤ smoothGrowthFactor k (modulusGrowthCost k) bulk.μ L := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hnR : (n:ℝ) ≤ (2:ℝ)^k*(bulkSize k L:ℝ)+2 := by exact_mod_cast hn
  have haR : (a:ℝ) ≤ residueCostExponent k := by exact_mod_cast ha
  have hb : (n:ℝ)+a ≤ modulusGrowthCost k*((bulkSize k L:ℝ)+1) := by
    unfold modulusGrowthCost
    nlinarith [Nat.cast_nonneg (bulkSize k L) (α:=ℝ),
      Nat.cast_nonneg (residueCostExponent k) (α:=ℝ),pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k,
      mul_nonneg (Nat.cast_nonneg (residueCostExponent k) (α:=ℝ)) (Nat.cast_nonneg (bulkSize k L) (α:=ℝ))]
  have hc : 0 ≤ modulusGrowthCost k*((bulkSize k L:ℝ)+1) := by unfold modulusGrowthCost; positivity
  calc
    _ = Real.exp (((n:ℝ)+a)*Real.log (M:ℝ)) := by rw [←Nat.cast_add,Real.exp_nat_mul,Real.exp_log hM0]
    _ ≤ Real.exp (modulusGrowthCost k*((bulkSize k L:ℝ)+1)*Real.exp (bulk.μ*L)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul hb hmod (Real.log_nonneg (by exact_mod_cast hM)) hc
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith : Real.exp (bulk.μ*L) ≤ Real.exp (bulk.μ*L)+1) hc)

theorem bulk_variation_prefactor_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) {L C D : ℝ} {M a : ℕ} (E : Finset ℕ) (hL : 0 ≤ L)
    (hn : Fintype.card ι ≤ 2^k*bulkSize k L+2) (ha : a ≤ residueCostExponent k)
    (hM : 0 < M) (hmod : Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L))
    (hZ : 0 < bulkNormalizer L E) (hz : L/1000 ≤ bulkNormalizer L E)
    (hD : 0 ≤ D) (hDb : D ≤ Real.exp (C*((bulkSize k L:ℝ)+1))) :
    2*((Fintype.card ι:ℝ)*D*meshWidth bulk L)*
      principalMass M (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => bulkNormalizer L E)*(M:ℝ)^(Fintype.card ι+a) ≤
    meshWidth bulk L*smoothGrowthFactor k
      (1+dimensionCoefficient k+|C|+modulusGrowthCost k) bulk.μ L := by
  let n := Fintype.card ι
  have hm := (bulk_principalMass_bounds (ι:=ι) M hM hL E hZ hz).2
  have hnG := (tensor_two_factors_le k n L bulk.μ hn).2
  have hDG := hDb.trans (amplitude_growth_le k (σ:=bulk.μ))
  have hMG := all_modulus_power_growth_le k hn ha hM hmod
  have hprod := mul_le_mul
    (mul_le_mul (mul_le_mul (two_le_growth k bulk.μ L) hnG
      (by positivity : 0 ≤ (n:ℝ)*2^n) (Real.exp_nonneg _)) hDG hD
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))) hMG
    (by positivity : 0 ≤ (M:ℝ)^(n+a))
    (mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _))
  calc
    _ ≤ 2*((n:ℝ)*D*meshWidth bulk L)*(2:ℝ)^n*(M:ℝ)^(n+a) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm (by unfold meshWidth; positivity)) (by positivity)
    _ = meshWidth bulk L*(2*((n:ℝ)*2^n)*D*(M:ℝ)^(n+a)) := by ring
    _ ≤ meshWidth bulk L*((smoothGrowthFactor k 1 bulk.μ L*
        smoothGrowthFactor k (dimensionCoefficient k) bulk.μ L)*
        smoothGrowthFactor k |C| bulk.μ L*smoothGrowthFactor k (modulusGrowthCost k) bulk.μ L) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _)
    _ = _ := by simp only [smoothGrowthFactor_mul]

theorem eventually_bulk_variation_error (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(M a:ℕ)(E:Finset ℕ)(D:ℝ), Fintype.card ι ≤ 2^k*bulkSize k L+2 →
      a ≤ residueCostExponent k → 0 < M → Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L) →
      E.card ≤ 2 → 0 ≤ D → D ≤ Real.exp (C*((bulkSize k L:ℝ)+1)) →
    2*((Fintype.card ι:ℝ)*D*meshWidth bulk L)*
      principalMass M (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => bulkNormalizer L E)*(M:ℝ)^(Fintype.card ι+a) ≤
      Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [eventually_variation_error bulk k
      (1+dimensionCoefficient k+|C|+modulusGrowthCost k) bulk.μ_pos.le bulk.μ_lt_δ,
    bulkNormalizer_bounds_eventually,eventually_ge_atTop (0:ℝ)] with L hbudget hnorm hL
  intro ι _ _ M a E D hn ha hM hmod hE hD hDb
  have hz := hnorm E hE
  apply (bulk_variation_prefactor_le k E hL hn ha hM hmod hz.1 hz.2.1 hD hDb).trans
  rw [meshWidth,smoothGrowthFactor,←Real.exp_add]
  convert hbudget using 1
  congr 1
  ring

end Ostmann.Arithmetic.HistoryBulkReplacementError

end

end OAI
