import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementErrorBasic
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellMeshCounts

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReplacementError
open Construction Conclusion HistoryBulkPriorGrid PrimeCellReplacement PrimeProgression
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget LogCellPartition Filter
open scoped BigOperators

theorem bulk_grid_card_le {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 ≤ L) :
    Fintype.card (GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
      (fun _ => meshWidth bulk L)) ≤ (meshIntervals bulk L)^Fintype.card ι := by
  have hlen : bulkLogUpper L-bulkLogLower L ≤ Real.exp (bulk.a₁*L) := by
    have hu : bulkLogUpper L ≤ Real.exp (bulk.a₁*L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by norm_num [bulk]) hL)
    have hl : 0 < bulkLogLower L := Real.exp_pos _
    linarith
  change Fintype.card (ι → Fin (gridCount (bulkLogLower L) (bulkLogUpper L)
    (meshWidth bulk L))) ≤ _
  rw [Fintype.card_fun,Fintype.card_fin]
  exact Nat.pow_le_pow_left (gridCount_le_ceiling (by unfold meshWidth; positivity) hlen) _

theorem bulk_ap_prefactor_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) {L C D A ε : ℝ} {M a : ℕ} (hL : 0 ≤ L)
    (hn : Fintype.card ι ≤ 2^k*bulkSize k L+2) (ha : a ≤ residueCostExponent k)
    (hM : 0 < M) (hmod : Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L))
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hDb : D ≤ Real.exp (C*((bulkSize k L:ℝ)+1)))
    (hAb : A ≤ Real.exp (C*((bulkSize k L:ℝ)+1))) :
    ((Fintype.card ι:ℝ)*D*meshWidth bulk L+A)*
      (Fintype.card (GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => meshWidth bulk L))*((Fintype.card ι:ℝ)*ε*2^Fintype.card ι))*
      (M:ℝ)^(Fintype.card ι+a) ≤
    jointMeshFactor bulk L (Fintype.card ι) M*
      smoothGrowthFactor k (2*dimensionCoefficient k+|C|+1+residueCostExponent k) bulk.μ L*ε := by
  let n := Fintype.card ι
  have hg : (Fintype.card (GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => meshWidth bulk L)):ℝ) ≤ (meshIntervals bulk L:ℝ)^n := by
    exact_mod_cast bulk_grid_card_le (ι:=ι) hL
  have hfirst := derivative_amplitude_growth_le k n hn hD hDb hAb
  have hsecond := (tensor_two_factors_le k n L bulk.μ hn).2
  have hthird := modulus_power_growth_le k ha hM hmod
  have hprod := mul_le_mul
    (mul_le_mul hfirst hsecond (by positivity : 0 ≤ (n:ℝ)*2^n) (Real.exp_nonneg _))
    hthird (by positivity : 0 ≤ (M:ℝ)^a)
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  have hbound : (((n:ℝ)*D*meshWidth bulk L+A)*((n:ℝ)*2^n))*(M:ℝ)^a ≤
      smoothGrowthFactor k (2*dimensionCoefficient k+|C|+1+residueCostExponent k) bulk.μ L := by
    apply hprod.trans_eq
    rw [smoothGrowthFactor_mul,smoothGrowthFactor_mul]
    congr 1
    ring
  calc
    _ ≤ ((n:ℝ)*D*meshWidth bulk L+A)*((meshIntervals bulk L:ℝ)^n*((n:ℝ)*ε*2^n))*(M:ℝ)^(n+a) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by unfold meshWidth; positivity)
      exact mul_le_mul_of_nonneg_right hg (by positivity)
    _ = jointMeshFactor bulk L n M*ε*((((n:ℝ)*D*meshWidth bulk L+A)*((n:ℝ)*2^n))*(M:ℝ)^a) := by
      simp only [jointMeshFactor,Nat.cast_mul,Nat.cast_pow,pow_add]
      ring
    _ ≤ jointMeshFactor bulk L n M*ε*
        smoothGrowthFactor k (2*dimensionCoefficient k+|C|+1+residueCostExponent k) bulk.μ L :=
      mul_le_mul_of_nonneg_left hbound (by unfold jointMeshFactor; positivity)
    _ = _ := by ring

theorem eventually_bulk_ap_error (k : ℕ) (C : ℝ) {K d : ℝ} (hK : 0 ≤ K) (hd : 0 < d) :
    ∀ᶠ L : ℝ in atTop, ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(M a:ℕ)(D A:ℝ), Fintype.card ι ≤ 2^k*bulkSize k L+2 →
      a ≤ residueCostExponent k → 0 < M → Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L) →
      0 ≤ D → 0 ≤ A → D ≤ Real.exp (C*((bulkSize k L:ℝ)+1)) →
      A ≤ Real.exp (C*((bulkSize k L:ℝ)+1)) →
    ((Fintype.card ι:ℝ)*D*meshWidth bulk L+A)*
      (Fintype.card (GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => meshWidth bulk L))*((Fintype.card ι:ℝ)*primeEnvelope bulk k 1 K d L*2^Fintype.card ι))*
      (M:ℝ)^(Fintype.card ι+a) ≤ Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [eventually_primeEnvelope_budget bulk k (C:=1)
      (D:=2*dimensionCoefficient k+|C|+1+residueCostExponent k) (A:=1)
      (by norm_num) (by norm_num) hK hd bulk.μ_pos.le bulk.μ_lt_δ.le,
    eventually_ge_atTop (0:ℝ)] with L hbudget hL
  intro ι _ _ M a D A hn ha hM hmod hD hA hDb hAb
  apply (bulk_ap_prefactor_le k hL hn ha hM hmod hD hA
    (show 0 ≤ primeEnvelope bulk k 1 K d L by unfold primeEnvelope; positivity) hDb hAb).trans
  simpa only [mul_one] using hbudget (Fintype.card ι) M hn hM hmod

end Ostmann.Arithmetic.HistoryBulkReplacementError

end

end OAI
