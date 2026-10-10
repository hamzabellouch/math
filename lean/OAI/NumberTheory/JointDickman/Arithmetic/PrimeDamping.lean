import OAI.NumberTheory.JointDickman.Analysis.CharacterPrimeCutoff

namespace OAI

/-! # Uniform error from damping prime reciprocal weights -/
namespace JointDickman
open Finset

lemma prime_reciprocal_damping {p δ : ℝ} (hp : 1 ≤ p) (_hδ : 0 ≤ δ) :
    p⁻¹ - p^(-(1+δ)) ≤ δ*(Real.log p/p) := by
  have hp0 : 0 < p := by linarith
  have he := Real.add_one_le_exp (-(δ*Real.log p))
  have hr : p^(-(1+δ)) = p⁻¹*Real.exp (-(δ*Real.log p)) := by
    rw [show -(1+δ) = -1 + -δ by ring,Real.rpow_add hp0,Real.rpow_neg_one,
      Real.rpow_def_of_pos hp0]
    congr 2
    ring
  rw [hr]
  have hm := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp0.le)
  change p⁻¹ * (-(δ*Real.log p)+1) ≤ p⁻¹ * Real.exp (-(δ*Real.log p)) at hm
  rw [div_eq_mul_inv]
  nlinarith

lemma primeCutoff_log_reciprocal_bound {X : ℝ} (hX : 1 ≤ X) :
    (∑ p ∈ primeCutoff X, Real.log p.val/(p.val:ℝ)) ≤
      Real.log X + (Real.log 4+4) := by
  rw [primeCutoff_sum (fun p : ℕ => Real.log (p:ℝ)/(p:ℝ)),prime_filter_Icc_eq_Ioc,
    Erdos970.Mertens.sum_log_prime_div_eq]
  linarith [Erdos970.Mertens.E₁p.le hX]

lemma primeCutoff_damping_bound {X δ : ℝ} (hX : 1 ≤ X) (hδ : 0 ≤ δ) :
    (∑ p ∈ primeCutoff X, (p.val:ℝ)⁻¹) -
      (∑ p ∈ primeCutoff X, (p.val:ℝ)^(-(1+δ))) ≤
      δ*(Real.log X+(Real.log 4+4)) := by
  calc
    _ = ∑ p ∈ primeCutoff X, ((p.val:ℝ)⁻¹-(p.val:ℝ)^(-(1+δ))) := by
      rw [sum_sub_distrib]
    _ ≤ ∑ p ∈ primeCutoff X, δ*(Real.log p.val/(p.val:ℝ)) := by
      apply sum_le_sum
      intro p _
      exact prime_reciprocal_damping (by exact_mod_cast p.property.one_le) hδ
    _ = δ*∑ p ∈ primeCutoff X, Real.log p.val/(p.val:ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeCutoff_log_reciprocal_bound hX) hδ

lemma primeCutoff_log_scale_damping {X : ℝ} (hX : 2 ≤ X) :
    (∑ p ∈ primeCutoff X, (p.val:ℝ)⁻¹) -
      (∑ p ∈ primeCutoff X, (p.val:ℝ)^(-(1+1/Real.log X))) ≤
      1+(Real.log 4+4)/Real.log 2 := by
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ Real.log 4+4 := by positivity
  calc
    _ ≤ (1/Real.log X)*(Real.log X+(Real.log 4+4)) :=
      primeCutoff_damping_bound (by linarith) (by positivity)
    _ = 1+(Real.log 4+4)/Real.log X := by field_simp
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_left hC hlog2
      (Real.log_le_log (by norm_num) hX)) _

end JointDickman

end OAI
