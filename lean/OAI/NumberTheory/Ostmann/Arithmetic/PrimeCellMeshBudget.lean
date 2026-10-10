import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellMeshGrowth

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellMeshBudget
open ScaleBudget Filter

theorem actual_coordinate_count_le (k n : ℕ) {L : ℝ} (hL : 1 ≤ L)
    (hn : n ≤ 2^k*Conclusion.bulkSize k L+2) :
    (n:ℝ) ≤ ((2:ℝ)^k*Conclusion.bulkScale k+2)*L := by
  have hm := (Conclusion.bulkSize_bounds k (by linarith : 0 ≤ L)).2
  have hh : (n:ℝ) ≤ (2:ℝ)^k*(Conclusion.bulkSize k L:ℝ)+2 := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hm (pow_nonneg (by norm_num : (0:ℝ)≤2) k)
  nlinarith

theorem actual_log_joint_mesh_card_le (r : Row) (k n M : ℕ) {L : ℝ}
    (hL : 1 ≤ L) (hn : n ≤ 2^k*Conclusion.bulkSize k L+2)
    (hM : 0 < M) (hmod : Real.log (M:ℝ) ≤ Real.exp (r.μ*L)) :
    Real.log (((meshIntervals r L)^n*M^n : ℕ):ℝ) ≤
      (((2:ℝ)^k*Conclusion.bulkScale k+2)*L)*
        (Real.exp (r.δ*L)+r.a₁*L+Real.log 4+Real.exp (r.μ*L)) := by
  apply (log_joint_mesh_card_le r (by linarith) n M hM hmod).trans
  apply mul_le_mul_of_nonneg_right (actual_coordinate_count_le k n hL hn)
  have ha := row_a₁_pos r
  have hlog : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  positivity

theorem eventually_variation_error (r : Row) (k : ℕ) (C : ℝ)
    {σ : ℝ} (hσ : 0 ≤ σ) (hgap : σ < r.δ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-Real.exp (r.δ*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)*Real.exp (σ*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)) ≤
      Real.exp (-Real.exp (r.target*L)) := by
  filter_upwards [eventually_double_exp_error (2*bulkCostConstant k C) 1
      hgap r.target_lt_δ (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℝ)] with L he hL
  apply le_trans _ he
  apply Real.exp_le_exp.mpr
  have hh := variation_cost_le k C hL hσ
  simp only [pow_one]
  linarith only [hh]

theorem eventually_joint_progression_error (r : Row) (k : ℕ) (C : ℝ)
    {σ c : ℝ} (hσ : σ ≤ r.δ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-c*Real.exp ((r.a₀/3)*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)*
          (Real.exp (r.δ*L)+L+Real.exp (r.μ*L)+Real.exp (σ*L))) ≤
      Real.exp (-Real.exp (r.target*L)) := by
  have hgap : r.δ < r.a₀/3 := by
    linarith [r.δ_lt_δ',r.δ'_lt_θ,r.zero_gap]
  filter_upwards [eventually_double_exp_error (4*bulkCostConstant k C) 2
      hgap (r.target_lt_δ.trans hgap) hc,
    eventually_ge_atTop (1:ℝ)] with L he hL
  apply le_trans _ he
  apply Real.exp_le_exp.mpr
  linarith only [joint_error_cost_le r k C hL hσ]

theorem eventually_joint_integer_error (r : Row) (k : ℕ) (C : ℝ)
    {σ c : ℝ} (hσ : σ ≤ r.δ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-c*Real.exp (r.a₀*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)*
          (Real.exp (r.δ*L)+L+Real.exp (r.μ*L)+Real.exp (σ*L))) ≤
      Real.exp (-Real.exp (r.target*L)) := by
  have hgap : r.δ < r.a₀ := by
    linarith [r.μ_pos,r.μ_lt_δ,r.δ_lt_δ',r.δ'_lt_θ,r.zero_gap]
  filter_upwards [eventually_double_exp_error (4*bulkCostConstant k C) 2
      hgap (r.target_lt_δ.trans hgap) hc,
    eventually_ge_atTop (1:ℝ)] with L he hL
  apply le_trans _ he
  apply Real.exp_le_exp.mpr
  linarith only [joint_error_cost_le r k C hL hσ]

theorem eventually_giant_and_bulk_errors (k : ℕ) (C : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      (Real.exp (-Real.exp (giant.δ*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)*Real.exp ((12/1000:ℝ)*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)) ≤ Real.exp (-Real.exp (giant.target*L))) ∧
      (Real.exp (-Real.exp (bulk.δ*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)*Real.exp ((1/1000:ℝ)*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)) ≤ Real.exp (-Real.exp (bulk.target*L))) ∧
      (Real.exp (-c*Real.exp ((giant.a₀/3)*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)*
          (Real.exp (giant.δ*L)+L+Real.exp (giant.μ*L)+Real.exp ((12/1000:ℝ)*L))) ≤
          Real.exp (-Real.exp (giant.target*L))) ∧
      (Real.exp (-c*Real.exp ((bulk.a₀/3)*L)+
        C*((Conclusion.bulkSize k L:ℝ)+1)*
          (Real.exp (bulk.δ*L)+L+Real.exp (bulk.μ*L)+Real.exp ((1/1000:ℝ)*L))) ≤
          Real.exp (-Real.exp (bulk.target*L))) := by
  filter_upwards [eventually_variation_error giant k C (by norm_num : (0:ℝ)≤12/1000)
      (by norm_num [giant]),
    eventually_variation_error bulk k C (by norm_num : (0:ℝ)≤1/1000) (by norm_num [bulk]),
    eventually_joint_progression_error giant k C (by norm_num [giant] : (12/1000:ℝ)≤giant.δ) hc,
    eventually_joint_progression_error bulk k C (by norm_num [bulk] : (1/1000:ℝ)≤bulk.δ) hc]
    with L h1 h2 h3 h4
  exact ⟨h1,h2,h3,h4⟩

end Ostmann.Arithmetic.PrimeCellMeshBudget

end

end OAI
