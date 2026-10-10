import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetMixedBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellActualErrorBudget
open ScaleBudget PrimeCellMeshBudget LogCellPartition PrimeProgression Filter

theorem harmonicIntegral_normalized_abs_le (M : ℕ) (hM : 0 < M)
    {lo hi Z A : ℝ} (hlo : 1 ≤ lo) (horder : lo ≤ hi)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ Real.exp A) :
    |harmonicIntegral M lo hi/Z| ≤ (hi-lo)*Real.exp A := by
  have htpos : (0:ℝ)<M.totient := by exact_mod_cast Nat.totient_pos.mpr hM
  have htone : (1:ℝ)≤M.totient := by exact_mod_cast Nat.totient_pos.mpr hM
  have htinv : (M.totient:ℝ)⁻¹ ≤ 1 := inv_le_one₀ htpos |>.mpr htone
  have hwidth : 0 ≤ hi-lo := sub_nonneg.mpr horder
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun t : ℝ => t⁻¹)
    (C:=1) (a:=lo) (b:=hi) (fun t ht => by
      rw [Set.uIoc_of_le horder] at ht
      have ht1 : 1 ≤ t := hlo.trans ht.1.le
      have ht0 : 0 < t := by linarith
      rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht0)]
      exact inv_le_one₀ ht0 |>.mpr ht1)
  simp only [Real.norm_eq_abs,one_mul,abs_of_nonneg hwidth] at hh
  rw [harmonicIntegral,abs_div,abs_mul,abs_of_nonneg (inv_nonneg.mpr htpos.le),abs_of_pos hZ,
    div_eq_mul_inv]
  calc
    _ ≤ (1*(hi-lo))*Real.exp A :=
      mul_le_mul (mul_le_mul htinv hh (abs_nonneg _) (by norm_num)) hZi
        (inv_nonneg.mpr hZ.le) (by positivity)
    _ = _ := by ring

theorem eventually_actual_primeCell_bounds (r : Row) (k : ℕ)
    {C K d : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hd : 0 < d) :
    ∀ᶠ L : ℝ in atTop, ∀ (M : ℕ) (lo hi Z : ℝ),
      0 < M → Real.exp (r.a₀*L) ≤ lo → lo ≤ hi → hi-lo ≤ meshWidth r L →
      0 < Z → Z⁻¹ ≤ Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)) →
      correctedPrimeError K d lo Z ≤ primeEnvelope r k C K d L ∧
        |harmonicIntegral M lo hi/Z|+primeEnvelope r k C K d L ≤ 2 := by
  have hδ : 0 < r.δ := r.μ_pos.trans r.μ_lt_δ
  filter_upwards [eventually_variation_error r k C (by norm_num : (0:ℝ)≤0) hδ,
    eventually_primeEnvelope_budget r k (D:=0) hC (by norm_num : (0:ℝ)≤1) hK hd
      (by norm_num : (0:ℝ)≤0) hδ.le,
    eventually_ge_atTop (0:ℝ)] with L hv he hL
  intro M lo hi Z hM hlo horder hwidth hZ hZi
  have hlo1 : 1 ≤ lo := (Real.one_le_exp (mul_nonneg (row_a₀_pos r).le hL)).trans hlo
  have hmass := harmonicIntegral_normalized_abs_le M hM hlo1 horder hZ hZi
  have htarget : Real.exp (-Real.exp (r.target*L)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg _))
  have henv : primeEnvelope r k C K d L ≤ 1 := by
    have hh := he 0 1 (by omega) (by norm_num) (by simpa using (Real.exp_nonneg (r.μ*L)))
    simpa only [jointMeshFactor,pow_zero,Nat.cast_one,mul_one,smoothGrowthFactor,
      zero_mul,Real.exp_zero,one_mul] using hh.trans htarget
  have hmass1 : |harmonicIntegral M lo hi/Z| ≤ 1 := by
    apply (hmass.trans (mul_le_mul_of_nonneg_right hwidth (Real.exp_nonneg _))).trans
    apply le_trans _ (hv.trans htarget)
    simp only [meshWidth,← Real.exp_add,zero_mul,Real.exp_zero,mul_one]
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ C*((Conclusion.bulkSize k L:ℝ)+1) := by positivity
    linarith
  exact ⟨correctedPrimeError_le_envelope r k hK hd hL hlo hZ hZi,by linarith⟩

end Ostmann.Arithmetic.PrimeCellActualErrorBudget

end

end OAI
