import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudget

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantReplacementError
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget Filter

def residueCostExponent (k : ℕ) : ℕ := 3+2^(k+1)

theorem residueCostExponent_mono {l k : ℕ} (hl : l≤k) :
    residueCostExponent l≤residueCostExponent k := by
  unfold residueCostExponent
  exact Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right hl 1)) 3

theorem modulus_power_growth_le (k : ℕ) {a M : ℕ} {L : ℝ}
    (ha : a≤residueCostExponent k) (hM : 0<M)
    (hmod : Real.log (M:ℝ)≤Real.exp (giant.μ*L)) :
    (M:ℝ)^a≤ smoothGrowthFactor k (residueCostExponent k) giant.μ L := by
  have hM0 : (0:ℝ)<M := by exact_mod_cast hM
  have haR : (a:ℝ)≤residueCostExponent k := by exact_mod_cast ha
  have hlog0 : 0≤Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hb := mul_le_mul haR hmod hlog0 (Nat.cast_nonneg _)
  have hbig : (residueCostExponent k:ℝ)*Real.exp (giant.μ*L)≤
      (residueCostExponent k:ℝ)*((Conclusion.bulkSize k L:ℝ)+1)*(Real.exp (giant.μ*L)+1) := by
    nlinarith [Nat.cast_nonneg (Conclusion.bulkSize k L) (α:=ℝ),
      Nat.cast_nonneg (residueCostExponent k) (α:=ℝ),Real.exp_pos (giant.μ*L),
      mul_nonneg (Nat.cast_nonneg (residueCostExponent k) (α:=ℝ))
        (Nat.cast_nonneg (Conclusion.bulkSize k L) (α:=ℝ)),
      mul_nonneg (mul_nonneg (Nat.cast_nonneg (residueCostExponent k) (α:=ℝ))
        (Nat.cast_nonneg (Conclusion.bulkSize k L) (α:=ℝ))) (Real.exp_nonneg (giant.μ*L))]
  calc
    _ = Real.exp ((a:ℝ)*Real.log (M:ℝ)) := by rw [Real.exp_nat_mul,Real.exp_log hM0]
    _ ≤ _ := Real.exp_le_exp.mpr (hb.trans hbig)

theorem modulus_growth_le (k : ℕ) (C : ℝ) {a M : ℕ} {L : ℝ}
    (ha : a≤residueCostExponent k) (hM : 0<M)
    (hmod : Real.log (M:ℝ)≤Real.exp (giant.μ*L)) :
    (M:ℝ)^a*smoothGrowthFactor k C giant.μ L≤
      smoothGrowthFactor k (C+residueCostExponent k) giant.μ L := by
  calc
    _ ≤ smoothGrowthFactor k (residueCostExponent k) giant.μ L*
        smoothGrowthFactor k C giant.μ L :=
      mul_le_mul_of_nonneg_right (modulus_power_growth_le k ha hM hmod) (Real.exp_nonneg _)
    _ = _ := by rw [smoothGrowthFactor_mul,add_comm]

theorem grid_modulus_growth_le (k : ℕ) (C : ℝ) {a M : ℕ} {L : ℝ}
    (ha : a≤residueCostExponent k) (hM : 0<M)
    (hmod : Real.log (M:ℝ)≤Real.exp (giant.μ*L)) :
    (meshIntervals giant L:ℝ)^2*(M:ℝ)^a*smoothGrowthFactor k C giant.μ L≤
      jointMeshFactor giant L 2 M*smoothGrowthFactor k (C+residueCostExponent k) giant.μ L := by
  have hm1 : (1:ℝ)≤M := by exact_mod_cast hM
  have hm2 : (1:ℝ)≤(M:ℝ)^2 := one_le_pow₀ hm1
  calc
    _ = (meshIntervals giant L:ℝ)^2*((M:ℝ)^a*smoothGrowthFactor k C giant.μ L) := by ring
    _ ≤ (meshIntervals giant L:ℝ)^2*smoothGrowthFactor k (C+residueCostExponent k) giant.μ L :=
      mul_le_mul_of_nonneg_left (modulus_growth_le k C ha hM hmod) (by positivity)
    _ ≤ _ := by
      unfold jointMeshFactor
      push_cast
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hm2) (Real.exp_nonneg _)

lemma correctedPrimeError_nonneg {K d lower Z : ℝ} (hK : 0≤K) (hZ : 0<Z) :
    0≤correctedPrimeError K d lower Z := by
  unfold correctedPrimeError
  positivity

end Ostmann.Arithmetic.HistoryGiantReplacementError

end

end OAI
