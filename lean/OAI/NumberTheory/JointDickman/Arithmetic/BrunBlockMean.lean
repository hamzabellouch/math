import OAI.NumberTheory.JointDickman.Arithmetic.BrunTruncationError

namespace OAI

/-! # Relative error for the mean of an even Brun truncation -/
namespace JointDickman
open Finset

 theorem sum_le_log_inverse_product (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    (∑ p ∈ P, g p) ≤ Real.log (∏ p ∈ P, (1-g p)⁻¹) := by
  rw [Real.log_prod (fun p hp => inv_ne_zero (by linarith [(hg p hp).2]))]
  apply sum_le_sum
  intro p hp
  rw [Real.log_inv]
  have h := Real.log_le_sub_one_of_pos (show 0 < 1-g p by linarith [(hg p hp).2])
  linarith

 theorem brunMean_nonneg (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) : 0 ≤ brunMean P g r := by
  classical
  apply sum_nonneg
  intro E hE
  exact mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hE) hg)
    (brunTruncation_nonneg E r)

 theorem brunMean_relative (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) {B : ℝ}
    (hB : (∏ p ∈ P, (1-g p)⁻¹) ≤ Real.exp B) :
    brunMean P g r ≤ (∏ p ∈ P, (1-g p)) * (1+Real.exp (4*B)/(4:ℝ)^r) := by
  have hpos : 0 < ∏ p ∈ P, (1-g p) := prod_pos (fun p hp => by linarith [(hg p hp).2])
  have hsum : (∑ p ∈ P, g p) ≤ B := by
    apply (sum_le_log_inverse_product P g hg).trans
    exact (Real.log_le_log (prod_pos (fun p hp => inv_pos.mpr (by linarith [(hg p hp).2]))) hB).trans_eq (Real.log_exp B)
  have hmul : 1 ≤ (∏ p ∈ P, (1-g p))*Real.exp B := by
    rw [prod_inv_distrib] at hB
    have h := mul_le_mul_of_nonneg_left hB hpos.le
    rwa [mul_inv_cancel₀ hpos.ne'] at h
  have he : Real.exp (3*B) ≤ (∏ p ∈ P, (1-g p))*Real.exp (4*B) := by
    have h := mul_le_mul_of_nonneg_right hmul (Real.exp_pos (3*B)).le
    rw [show 4*B = B+3*B by ring, Real.exp_add]
    nlinarith
  calc
    _ ≤ (∏ p ∈ P, (1-g p)) + Real.exp (3*B)/(4:ℝ)^r :=
      brunMean_le P g r (fun p hp => ⟨(hg p hp).1,(hg p hp).2.le⟩) hsum
    _ ≤ (∏ p ∈ P, (1-g p)) + ((∏ p ∈ P, (1-g p))*Real.exp (4*B))/(4:ℝ)^r :=
      add_le_add le_rfl (div_le_div_of_nonneg_right he (by positivity))
    _ = _ := by ring

end JointDickman

end OAI
