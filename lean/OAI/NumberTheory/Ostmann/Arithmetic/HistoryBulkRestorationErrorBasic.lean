import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGridRestoration
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellMeshGrowth
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkRestorationError
open Construction HistoryBulkPriorGrid ScaleBudget PrimeCellMeshBudget Filter
open scoped BigOperators

theorem pow_sub_one_le {r δ : ℝ} (hr : 1 ≤ r) (h4 : r ≤ 4)
    (hδ : r-1 ≤ δ) (n : ℕ) : r^n-1 ≤ δ*(n : ℝ)*4^n := by
  have hs : (∑ i ∈ Finset.range n, r^i) ≤ (n : ℝ)*4^n := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, (4 : ℝ)^n := by
        apply Finset.sum_le_sum
        intro i hi
        exact (pow_le_pow_left₀ (by linarith : 0 ≤ r) h4 i).trans
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (Finset.mem_range.mp hi).le)
      _ = _ := by simp
  rw [← geom_sum_mul r n]
  calc
    _ ≤ ((n : ℝ)*4^n)*(r-1) := mul_le_mul_of_nonneg_right hs (by linarith)
    _ ≤ ((n : ℝ)*4^n)*δ := mul_le_mul_of_nonneg_left hδ (by positivity)
    _ = _ := by ring

theorem ratio_pow_error_eventually :
    ∀ᶠ L : ℝ in atTop, ∀ E : Finset ℕ, E.card ≤ 2 → ∀ n : ℕ,
      0 ≤ bulkFullMassRatio L E^n-1 ∧
      bulkFullMassRatio L E^n-1 ≤
        Real.exp (2+(1+Real.log 4)*(n : ℝ)-Real.exp ((1/250 : ℝ)*L)) := by
  filter_upwards [RepeatedPriorBounds.bulk_mass_lower_eventually,
    eventually_ge_atTop (1000 : ℝ)] with L hZ hL
  intro E hE n
  have hnorm : 1 ≤ bulkNormalizer L E := by
    have hh := hZ E hE
    change L/1000 ≤ bulkNormalizer L E at hh
    linarith
  have hpos : 0 < bulkNormalizer L E := by linarith
  have hr := bulkFullMassRatio_bounds L E hpos
  have hcap : bulkRestorationCap L E ≤ 3*Real.exp (-bulkLogLower L) :=
    (bulkRestorationCap_le_three L E hpos hE).trans
      (div_le_self (by positivity) hnorm)
  have hsmall : Real.exp (-bulkLogLower L) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg _))
  have h4 : bulkFullMassRatio L E ≤ 4 := by nlinarith only [hr.2,hcap,hsmall]
  have hpow := pow_sub_one_le (δ := 3*Real.exp (-bulkLogLower L)) hr.1 h4 (by linarith only [hr.2,hcap]) n
  have hnexp : (n : ℝ) ≤ Real.exp (n : ℝ) := by linarith [Real.add_one_le_exp (n : ℝ)]
  have h4exp : (4 : ℝ)^n = Real.exp ((n : ℝ)*Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  refine ⟨sub_nonneg.mpr (one_le_pow₀ hr.1), hpow.trans ?_⟩
  calc
    _ = 3*Real.exp (-bulkLogLower L)*((n : ℝ)*4^n) := by ring
    _ ≤ Real.exp 2*Real.exp (-bulkLogLower L)*
        (Real.exp (n : ℝ)*Real.exp ((n : ℝ)*Real.log 4)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
      · rw [← h4exp]
        exact mul_le_mul_of_nonneg_right hnexp (by positivity)
      · positivity
      · positivity
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      unfold bulkLogLower
      congr 1
      ring

def restorationCost (k : ℕ) (C : ℝ) : ℝ :=
  2+(1+Real.log 4)*((2 : ℝ)^k*Conclusion.bulkScale k)+bulkCostConstant k C+
    (2 : ℝ)^k*Conclusion.bulkScale k+(3+(2 : ℝ)^(k+1))

theorem restoration_cost_le (k : ℕ) (C : ℝ) {L : ℝ} (hL : 1 ≤ L)
    {n a : ℕ} (hn : n ≤ 2^k*Conclusion.bulkSize k L) (ha : a ≤ 3+2^(k+1)) :
    2+(1+Real.log 4)*(n : ℝ)+((n : ℝ)+(a : ℝ))*Real.exp (bulk.μ*L)+
      C*((Conclusion.bulkSize k L : ℝ)+1) ≤
      restorationCost k C*L*Real.exp (bulk.μ*L) := by
  have hL0 : 0 ≤ L := by linarith
  have he : 1 ≤ Real.exp (bulk.μ*L) := Real.one_le_exp (mul_nonneg bulk.μ_pos.le hL0)
  have hb : 0 ≤ (2 : ℝ)^k*Conclusion.bulkScale k := by unfold Conclusion.bulkScale; positivity
  have hlog : 0 ≤ 1+Real.log 4 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hnR : (n : ℝ) ≤ (2 : ℝ)^k*(Conclusion.bulkSize k L : ℝ) := by exact_mod_cast hn
  have hnL : (n : ℝ) ≤ ((2 : ℝ)^k*Conclusion.bulkScale k)*L := by
    exact hnR.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (Conclusion.bulkSize_bounds k hL0).2 (by positivity : (0 : ℝ) ≤ (2 : ℝ)^k))
  have haR : (a : ℝ) ≤ 3+(2 : ℝ)^(k+1) := by exact_mod_cast ha
  have haL : (a : ℝ) ≤ (3+(2 : ℝ)^(k+1))*L :=
    haR.trans (le_mul_of_one_le_right (by positivity) hL)
  have hdim := mul_le_mul_of_nonneg_right (add_le_add hnL haL) (Real.exp_nonneg (bulk.μ*L))
  have hpoly : 2+(1+Real.log 4)*(n : ℝ)+C*((Conclusion.bulkSize k L : ℝ)+1) ≤
      (2+(1+Real.log 4)*((2 : ℝ)^k*Conclusion.bulkScale k)+bulkCostConstant k C)*L := by
    have hc := actual_bulk_cost_le k C hL
    have hh := mul_le_mul_of_nonneg_left hnL hlog
    nlinarith only [hc,hh,hL]
  have hpolyExp := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (2+(1+Real.log 4)*((2 : ℝ)^k*Conclusion.bulkScale k)+bulkCostConstant k C)*L by
      exact mul_nonneg (by positivity [bulkCostConstant_pos k C]) hL0)
  unfold restorationCost
  nlinarith only [hdim,hpoly,hpolyExp]

end Ostmann.Arithmetic.HistoryBulkRestorationError

end

end OAI
