import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorReplacementSelected
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudget
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReplacementError
open Construction Conclusion HistoryBulkPriorGrid PrimeCellReplacement PrimeProgression
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget LogCellPartition Filter
open scoped BigOperators

theorem bulkNormalizer_bounds_eventually :
    ∀ᶠ L : ℝ in atTop, ∀E:Finset ℕ,E.card ≤ 2 →
      0 < bulkNormalizer L E ∧ L/1000 ≤ bulkNormalizer L E ∧ (bulkNormalizer L E)⁻¹ ≤ 1 := by
  filter_upwards [RepeatedPriorBounds.bulk_mass_lower_eventually,eventually_ge_atTop (1000:ℝ)] with L hZ hL
  intro E hE
  have hz := hZ E hE
  change L/1000 ≤ bulkNormalizer L E at hz
  have hp : 0 < bulkNormalizer L E := by linarith
  exact ⟨hp,hz,(inv_le_one₀ hp).mpr (by linarith)⟩

theorem bulk_harmonicIntegral (M : ℕ) (L : ℝ) :
    harmonicIntegral M (bulkLogLower L) (bulkLogUpper L) = (M.totient:ℝ)⁻¹*(L/500) := by
  rw [harmonicIntegral,bulkLogLower,bulkLogUpper,integral_inv_of_pos (Real.exp_pos _) (Real.exp_pos _),
    Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
  simp only [Real.log_exp]
  ring

theorem bulk_principalMass_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (hM : 0 < M) {L : ℝ} (hL : 0 ≤ L) (E : Finset ℕ)
    (hZ : 0 < bulkNormalizer L E) (hz : L/1000 ≤ bulkNormalizer L E) :
    0 ≤ principalMass M (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
      (fun _ => bulkNormalizer L E) ∧
    principalMass M (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
      (fun _ => bulkNormalizer L E) ≤ (2:ℝ)^Fintype.card ι := by
  have ht : (0:ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr hM
  have hti : (M.totient:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ ht).mpr (by exact_mod_cast Nat.totient_pos.mpr hM)
  have hsingle : 0 ≤ harmonicIntegral M (bulkLogLower L) (bulkLogUpper L)/bulkNormalizer L E ∧
      harmonicIntegral M (bulkLogLower L) (bulkLogUpper L)/bulkNormalizer L E ≤ 2 := by
    rw [bulk_harmonicIntegral]
    constructor
    · positivity
    · apply (div_le_iff₀ hZ).mpr
      have hh := mul_le_mul_of_nonneg_right hti (show 0 ≤ L/500 by positivity)
      nlinarith
  unfold principalMass
  exact ⟨Finset.prod_nonneg (fun i _ => hsingle.1),by
    simpa using Finset.prod_le_prod₀ (fun i _ => hsingle.1) (fun i (_:i∈Finset.univ) => hsingle.2)⟩

def residueCostExponent (k : ℕ) : ℕ := 3+2^(k+1)

theorem modulus_power_growth_le (k : ℕ) {a M : ℕ} {L : ℝ}
    (ha : a ≤ residueCostExponent k) (hM : 0 < M)
    (hmod : Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L)) :
    (M:ℝ)^a ≤ smoothGrowthFactor k (residueCostExponent k) bulk.μ L := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have haR : (a:ℝ) ≤ residueCostExponent k := by exact_mod_cast ha
  have hlog0 : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hb := mul_le_mul haR hmod hlog0 (Nat.cast_nonneg _)
  have hbig : (residueCostExponent k:ℝ)*Real.exp (bulk.μ*L) ≤
      (residueCostExponent k:ℝ)*((bulkSize k L:ℝ)+1)*(Real.exp (bulk.μ*L)+1) := by
    have hh := mul_le_mul (show (1:ℝ) ≤ (bulkSize k L:ℝ)+1 by linarith [Nat.cast_nonneg (bulkSize k L) (α:=ℝ)])
      (show Real.exp (bulk.μ*L) ≤ Real.exp (bulk.μ*L)+1 by linarith) (Real.exp_nonneg _) (by positivity)
    simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (residueCostExponent k): (0:ℝ) ≤ _)
  calc
    _ = Real.exp ((a:ℝ)*Real.log (M:ℝ)) := by rw [Real.exp_nat_mul,Real.exp_log hM0]
    _ ≤ _ := Real.exp_le_exp.mpr (hb.trans hbig)

theorem growth_mono (k : ℕ) {C D σ L : ℝ} (h : C ≤ D) :
    smoothGrowthFactor k C σ L ≤ smoothGrowthFactor k D σ L := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity)

theorem growth_one_le (k : ℕ) {C σ L : ℝ} (hC : 0 ≤ C) :
    1 ≤ smoothGrowthFactor k C σ L := Real.one_le_exp (by positivity)

theorem two_le_growth (k : ℕ) (σ L : ℝ) : 2 ≤ smoothGrowthFactor k 1 σ L := by
  apply (show (2:ℝ) ≤ Real.exp 1 by linarith [Real.add_one_le_exp 1]).trans
  apply Real.exp_le_exp.mpr
  nlinarith [Nat.cast_nonneg (bulkSize k L) (α:=ℝ),Real.exp_pos (σ*L),
    mul_nonneg (Nat.cast_nonneg (bulkSize k L) (α:=ℝ)) (Real.exp_nonneg (σ*L))]

theorem amplitude_growth_le (k : ℕ) {C σ L : ℝ} :
    Real.exp (C*((bulkSize k L:ℝ)+1)) ≤ smoothGrowthFactor k |C| σ L := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (le_abs_self C) (show 0 ≤ (bulkSize k L:ℝ)+1 by positivity)
  nlinarith [mul_nonneg (show 0 ≤ |C| *((bulkSize k L:ℝ)+1) by positivity) (Real.exp_nonneg (σ*L))]

theorem derivative_amplitude_growth_le (k n : ℕ) {C L D A : ℝ}
    (hn : n ≤ 2^k*bulkSize k L+2) (hD : 0 ≤ D)
    (hDb : D ≤ Real.exp (C*((bulkSize k L:ℝ)+1)))
    (hAb : A ≤ Real.exp (C*((bulkSize k L:ℝ)+1))) :
    (n:ℝ)*D*meshWidth bulk L+A ≤
      smoothGrowthFactor k (dimensionCoefficient k+|C|+1) bulk.μ L := by
  have hmesh : meshWidth bulk L ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg _))
  have hnG : (n:ℝ) ≤ smoothGrowthFactor k (dimensionCoefficient k) bulk.μ L := by
    apply le_trans _ (tensor_two_factors_le k n L bulk.μ hn).2
    exact le_mul_of_one_le_right (Nat.cast_nonneg n) (one_le_pow₀ (by norm_num))
  have hDgrowth := hDb.trans (amplitude_growth_le k (σ:=bulk.μ))
  have hAgrowth := hAb.trans (amplitude_growth_le k (σ:=bulk.μ))
  have hmul : (n:ℝ)*D*meshWidth bulk L ≤
      smoothGrowthFactor k (dimensionCoefficient k+|C|) bulk.μ L := by
    apply (mul_le_mul_of_nonneg_left hmesh (mul_nonneg (Nat.cast_nonneg n) hD)).trans
    rw [mul_one,←smoothGrowthFactor_mul]
    exact mul_le_mul hnG hDgrowth hD (Real.exp_nonneg _)
  have hA' : A ≤ smoothGrowthFactor k (dimensionCoefficient k+|C|) bulk.μ L :=
    hAgrowth.trans (growth_mono k (by unfold dimensionCoefficient; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k]))
  calc
    _ ≤ 2*smoothGrowthFactor k (dimensionCoefficient k+|C|) bulk.μ L := by linarith
    _ ≤ smoothGrowthFactor k 1 bulk.μ L*smoothGrowthFactor k (dimensionCoefficient k+|C|) bulk.μ L :=
      mul_le_mul_of_nonneg_right (two_le_growth k bulk.μ L) (Real.exp_nonneg _)
    _ = _ := by rw [smoothGrowthFactor_mul]; congr 1; ring

end Ostmann.Arithmetic.HistoryBulkReplacementError

end

end OAI
