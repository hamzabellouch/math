import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.TreeHeight
import OAI.Combinatorics.SharpRamsey.Parameters.BookScales
import OAI.Combinatorics.SharpRamsey.Execution.OutputCost

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma eventually_monomial_le_power (C a b ε : ℝ) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x^b := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-b)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0:ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-b))*x^b := by rw [mul_assoc, ←rpow_add hx0]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hx.le (rpow_nonneg hx0.le _)

lemma P_upper_D {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0 < η)
    (had : Admissible σ η D R) : scaleP σ η D R ≤ 4*D*σ^(9*beta η) := by
  have hb := beta_pos hη
  have hpow : 1 ≤ σ^beta η := one_le_rpow hσ hb.le
  have hD : 0 ≤ D := (rpow_nonneg (by linarith : 0 ≤ σ) _).trans had.D_lower
  have hR : (R:ℝ) ≤ 4*σ^beta η := by linarith [had.R_upper]
  calc
    _ ≤ (D*σ^(8*beta η))*(4*σ^beta η) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ = _ := by
      have hp : σ^(8*beta η)*σ^beta η = σ^(9*beta η) := by
        rw [←rpow_add (by linarith : 0 < σ)]
        congr 1
        ring
      linear_combination (4*D)*hp

theorem eventually_literal_cost_contraction (η A B C c : ℝ)
    (hη : 0 < η) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D P h w k : ℝ,
      exp σ = q → 1 ≤ D → 0 ≤ P → P ≤ 4*D*σ^(9*beta η) →
      0 ≤ h → h ≤ σ^beta η → 0 ≤ w → w*D ≤ C*σ^(1+η/2) →
      c*q*σ^(1+η) ≤ k →
      A*q*P*h*(σ+w*P)+B*w*σ ≤ D*σ^(-η/3)*k := by
  have hb := beta_pos hη
  have hgap1 : 1+10*beta η < 1+2*η/3 := by unfold beta; linarith
  have hgap2 : 1+η/2+19*beta η < 1+2*η/3 := by unfold beta; linarith
  have ht := ScaleSelection.eventually_polynomial_exp_neg_rpow_lt
    (B*C) (1-η/6) 1 1 (c/3) (by norm_num) (by norm_num) (by positivity)
  filter_upwards [eventually_monomial_le_power (4*A) (1+10*beta η) (1+2*η/3)
      (c/3) hgap1 (by positivity),
    eventually_monomial_le_power (16*A*C) (1+η/2+19*beta η) (1+2*η/3)
      (c/3) hgap2 (by positivity), ht, eventually_ge_atTop (1:ℝ)]
    with σ h1 h2 h3 hσ q D P h w k hq hD hP hPup hh hhu hw hwD hk
  have hσ0 : 0 < σ := by linarith
  have hq0 : 0 < q := hq ▸ exp_pos _
  have hD0 : 0 < D := by linarith
  have hw' : w ≤ C*σ^(1+η/2) := by nlinarith
  have hf1 : A*q*P*h*σ ≤ (4*A)*σ^(1+10*beta η)*q*D := by
    calc
      _ ≤ A*q*(4*D*σ^(9*beta η))*(σ^beta η)*σ := by gcongr
      _ = _ := by
        have hp : σ^(9*beta η)*σ^beta η*σ = σ^(1+10*beta η) := by
          calc
            _ = σ^(9*beta η+beta η)*σ^(1:ℝ) := by rw [rpow_add hσ0, rpow_one]
            _ = _ := by rw [←rpow_add hσ0]; congr 1; ring
        linear_combination (A*q*4*D)*hp
  have hf2 : A*q*P*h*(w*P) ≤ (16*A*C)*σ^(1+η/2+19*beta η)*q*D := by
    calc
      _ ≤ A*q*(4*D*σ^(9*beta η))*(σ^beta η)*(w*(4*D*σ^(9*beta η))) := by gcongr
      _ = (16*A*q*D)*(w*D)*(σ^(9*beta η)*σ^beta η*σ^(9*beta η)) := by ring
      _ ≤ (16*A*q*D)*(C*σ^(1+η/2))*(σ^(9*beta η)*σ^beta η*σ^(9*beta η)) := by gcongr
      _ = _ := by
        have hp : σ^(1+η/2)*(σ^(9*beta η)*σ^beta η*σ^(9*beta η)) =
            σ^(1+η/2+19*beta η) := by
          rw [←rpow_add hσ0, ←rpow_add hσ0, ←rpow_add hσ0]
          congr 1
          ring
        linear_combination (16*A*q*D*C)*hp
  have hf3 : B*w*σ ≤ (c/3)*σ^(1+2*η/3)*q*D := by
    have he3 : B*C*σ^(1-η/6)*exp (-σ) ≤ c/3 := by
      simpa only [rpow_one, one_mul, neg_one_mul] using h3.le
    have h31 : B*C*σ^(1-η/6) ≤ (c/3)*q := by
      have hh := mul_le_mul_of_nonneg_right he3 (exp_nonneg σ)
      rw [mul_assoc (B*C*σ^(1-η/6)), ←exp_add, neg_add_cancel, exp_zero, mul_one] at hh
      simpa only [hq] using hh
    have h32 := mul_le_mul_of_nonneg_right h31 (rpow_nonneg hσ0.le (1+2*η/3))
    have he : σ^(1-η/6)*σ^(1+2*η/3) = σ^(2+η/2) := by
      rw [←rpow_add hσ0]
      congr 1
      ring
    rw [mul_assoc (B*C), he] at h32
    calc
      _ ≤ B*(C*σ^(1+η/2))*σ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw' hB) le_rfl hσ0.le
          (mul_nonneg hB (mul_nonneg hC (rpow_nonneg hσ0.le _)))
      _ = B*C*σ^(2+η/2) := by
        have hp : σ^(1+η/2)*σ = σ^(2+η/2) := by
          calc
            _ = σ^(1+η/2)*σ^(1:ℝ) := by rw [rpow_one]
            _ = _ := by rw [←rpow_add hσ0]; congr 1; ring
        linear_combination (B*C)*hp
      _ ≤ (c/3)*q*σ^(1+2*η/3) := h32
      _ ≤ (c/3)*σ^(1+2*η/3)*q*D := by
        nlinarith [mul_le_mul_of_nonneg_left hD
          (by positivity : 0 ≤ (c/3)*q*σ^(1+2*η/3))]
  have h1' := mul_le_mul_of_nonneg_right h1 (mul_nonneg hq0.le hD0.le)
  have h2' := mul_le_mul_of_nonneg_right h2 (mul_nonneg hq0.le hD0.le)
  have hk' := mul_le_mul_of_nonneg_left hk (mul_nonneg hD0.le (rpow_nonneg hσ0.le (-η/3)))
  have he : D*σ^(-η/3)*(c*q*σ^(1+η)) = c*σ^(1+2*η/3)*q*D := by
    have hp : σ^(-η/3)*σ^(1+η)=σ^(1+2*η/3) := by
      rw [←rpow_add hσ0]
      congr 1
      ring
    linear_combination (D*c*q)*hp
  rw [he] at hk'
  nlinarith only [hf1,hf2,hf3,h1',h2',hk']
end
end SharpLogRamsey.SourceScales

end

end OAI
