import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetCost

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellActualErrorBudget
open ScaleBudget PrimeCellMeshBudget Filter

lemma row_a₀_pos (r : Row) : 0 < r.a₀ := by
  linarith [r.μ_pos,r.μ_lt_δ,r.δ_lt_δ',r.δ'_lt_θ,r.zero_gap]

lemma smoothGrowth_mul_normalizer_le (k : ℕ) {C σ L : ℝ} (hC : 0 ≤ C) :
    smoothGrowthFactor k C σ L*Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)) ≤
      smoothGrowthFactor k (2*C) σ L := by
  unfold smoothGrowthFactor
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm : 0 ≤ C*((Conclusion.bulkSize k L:ℝ)+1) := by positivity
  nlinarith [Real.exp_pos (σ*L)]

theorem eventually_modulus_admissible (r : Row) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ L : ℝ in atTop, ∀ (M : ℕ) (lower : ℝ), 0 < M →
      Real.log (M:ℝ) ≤ Real.exp (r.μ*L) → Real.exp (r.a₀*L) ≤ lower →
      (M:ℝ) ≤ Real.exp (d*lower^(1/3:ℝ)) := by
  have hgap : r.μ < r.a₀/3 := by
    linarith [r.μ_lt_δ,r.δ_lt_δ',r.δ'_lt_θ,r.zero_gap]
  filter_upwards [eventually_poly_exp_le 1 0 hgap hd] with L hL
  simp only [pow_zero,mul_one,one_mul] at hL
  intro M lower hM hmod hlower
  have hpow := Real.rpow_le_rpow (Real.exp_nonneg (r.a₀*L)) hlower (by norm_num : (0:ℝ)≤1/3)
  rw [← Real.exp_mul] at hpow
  have hpow' : Real.exp ((r.a₀/3)*L) ≤ lower^(1/3:ℝ) := by
    convert hpow using 1; congr 1; ring
  have hh := hmod.trans (hL.trans (mul_le_mul_of_nonneg_left hpow' hd.le))
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  simpa only [Real.exp_log hMp] using Real.exp_le_exp.mpr hh

theorem eventually_correctedPrimeError_budget (r : Row) (k : ℕ)
    {C A K d σ : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hK : 0 ≤ K) (hd : 0 < d)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ r.δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (n M : ℕ) (lower Z : ℝ),
      n ≤ 2^k*Conclusion.bulkSize k L+2 → 0 < M →
      Real.log (M:ℝ) ≤ Real.exp (r.μ*L) → Real.exp (r.a₀*L) ≤ lower →
      0 < Z → Z⁻¹ ≤ Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)) →
      jointMeshFactor r L n M*smoothGrowthFactor k C σ L*A*
        correctedPrimeError K d lower Z ≤ Real.exp (-Real.exp (r.target*L)) := by
  let c : ℝ := min d 1
  have hc : 0 < c := lt_min hd (by norm_num)
  filter_upwards [eventually_weighted_progression_decay r k (2*C) (A*(K+1)) hσ0 hσ hc,
    eventually_ge_atTop (0:ℝ)] with L hbudget hL
  intro n M lower Z hn hM hmod hlower hZ hZi
  have he := correctedPrimeError_le hK hc.le (min_le_left d 1) (min_le_right d 1)
    (row_a₀_pos r).le hL hlower hZ hZi
  have hfactor : 0 ≤ jointMeshFactor r L n M := by unfold jointMeshFactor; positivity
  have hgrowth : 0 ≤ smoothGrowthFactor k C σ L := Real.exp_nonneg _
  calc
    _ ≤ jointMeshFactor r L n M*smoothGrowthFactor k C σ L*A*
        ((K+1)*Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)-c*Real.exp ((r.a₀/3)*L))) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg hfactor hgrowth) hA)
    _ = jointMeshFactor r L n M*
        (smoothGrowthFactor k C σ L*Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)))*
        (A*(K+1))*Real.exp (-c*Real.exp ((r.a₀/3)*L)) := by
      rw [sub_eq_add_neg,Real.exp_add,← neg_mul]
      ring
    _ ≤ jointMeshFactor r L n M*smoothGrowthFactor k (2*C) σ L*
        (A*(K+1))*Real.exp (-c*Real.exp ((r.a₀/3)*L)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (smoothGrowth_mul_normalizer_le k hC) hfactor) (by positivity)
    _ ≤ _ := hbudget n M hn hM hmod

theorem eventually_giant_bulk_correctedPrimeError_budget (k : ℕ)
    {C A K d : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hK : 0 ≤ K) (hd : 0 < d) :
    ∀ᶠ L : ℝ in atTop, ∀ (n M : ℕ) (lower Z : ℝ),
      n ≤ 2^k*Conclusion.bulkSize k L+2 → 0 < M → 0 < Z →
      Z⁻¹ ≤ Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)) →
      (Real.log (M:ℝ) ≤ Real.exp (giant.μ*L) → Real.exp (giant.a₀*L) ≤ lower →
        jointMeshFactor giant L n M*smoothGrowthFactor k C (12/1000) L*A*
          correctedPrimeError K d lower Z ≤ Real.exp (-Real.exp (giant.target*L))) ∧
      (Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L) → Real.exp (bulk.a₀*L) ≤ lower →
        jointMeshFactor bulk L n M*smoothGrowthFactor k C (1/1000) L*A*
          correctedPrimeError K d lower Z ≤ Real.exp (-Real.exp (bulk.target*L))) := by
  filter_upwards [eventually_correctedPrimeError_budget giant k hC hA hK hd
      (by norm_num : (0:ℝ)≤12/1000) (by norm_num [giant]),
    eventually_correctedPrimeError_budget bulk k hC hA hK hd
      (by norm_num : (0:ℝ)≤1/1000) (by norm_num [bulk])] with L hg hb
  intro n M lower Z hn hM hZ hZi
  exact ⟨fun hmod hlo => hg n M lower Z hn hM hmod hlo hZ hZi,
    fun hmod hlo => hb n M lower Z hn hM hmod hlo hZ hZi⟩

end Ostmann.Arithmetic.PrimeCellActualErrorBudget

end

end OAI
