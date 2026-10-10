import OAI.MeasureTheory.Falconer.Radial.PlateScales
import OAI.MeasureTheory.Falconer.Estimates.DyadicLossAbsorption

namespace OAI

/-! # Uniform scale choices for the initial block and the later plate losses -/

namespace Falconer
open Filter
open scoped Topology

theorem eventually_plate_geometry (M A : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      10*A*(plateScale j)^(1/8:ℝ) ≤ 1 ∧
      2*M*(plateScale j)^(1/8:ℝ)+3*A*(plateScale j)^(1/4:ℝ) ≤
        plateScale (j/32) := by
  have hs := eventually_const_mul_rpow_lt (by norm_num : (0:ℝ) < 1/8) (10*A)
  have h₁ := eventually_const_mul_rpow_lt (by norm_num : (1/32:ℝ) < 1/8) (4*M)
  have h₂ := eventually_const_mul_rpow_lt (by norm_num : (1/32:ℝ) < 1/4) (6*A)
  filter_upwards [plateScale_tendsto.eventually hs,plateScale_tendsto.eventually h₁,
    plateScale_tendsto.eventually h₂] with j hj h₁j h₂j
  refine ⟨by simpa only [Real.rpow_zero] using hj.2.le,?_⟩
  apply (show 2*M*(plateScale j)^(1/8:ℝ)+3*A*(plateScale j)^(1/4:ℝ) ≤
    (plateScale j)^(1/32:ℝ) from by linarith only [h₁j.2,h₂j.2]).trans
  exact plateScale_div_lower j

theorem eventually_initial_plate_card {b A : ℝ} (hb : 0 < b) (hA : 1 ≤ A) :
    ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      (n:ℝ) ≤ ((63*j:ℕ):ℝ)*A*(plateScale j)^(-64*b) →
      (n:ℝ) ≤ A*(plateScale j)^(-128*b) := by
  have he := eventually_dyadic_loss_absorption
    (show 64*b < 128*b by linarith only [hb]) (63*A)
  filter_upwards [plateScale_tendsto.eventually he] with j hj
  intro n hn
  have hlog : 1-Real.log (plateScale j)/Real.log 2 = (j:ℝ)+1 := by
    rw [plateScale_eq]
    exact dyadic_log_depth j
  rw [hlog] at hj
  have hcoeff : ((63*j:ℕ):ℝ)*A ≤ 63*A*((j:ℝ)+1) := by
    push_cast
    nlinarith only [hA]
  have hbnd : 63*A*((j:ℝ)+1)*(plateScale j)^(-64*b) ≤
      (plateScale j)^(-128*b) := by simpa only [neg_mul] using hj.2
  apply (hn.trans ((mul_le_mul_of_nonneg_right hcoeff
    (Real.rpow_nonneg (plateScale_pos _).le _)).trans hbnd)).trans
  exact le_mul_of_one_le_left (Real.rpow_nonneg (plateScale_pos _).le _) hA

theorem plate_cluster_width_tendsto (M A : ℝ) :
    Tendsto (fun j => 2*M*(plateScale j)^(1/8:ℝ)+3*A*(plateScale j)^(1/4:ℝ))
      atTop (𝓝 (0:ℝ)) := by
  simpa only [mul_zero,zero_add] using
    ((plateScale_power_tendsto (by norm_num : (0:ℝ) < 1/8)).const_mul (2*M)).add
      ((plateScale_power_tendsto (by norm_num : (0:ℝ) < 1/4)).const_mul (3*A))

end Falconer

end OAI
