import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialDifference

namespace OAI

/-! Uniform dependence of the actual amplitude potential on c and b. -/

open Set
namespace DefocusingNLS

theorem radialVelocityRatio_parameter_difference (c d R : ℝ) (A : ℝ → ℝ)
    (hA : Continuous A) (hAI : ∀ t ∈ Icc 0 R, A t ∈ Icc (999/1000 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc 0 R) :
    |radialVelocityRatio c A r-radialVelocityRatio d A r| ≤ |c-d|/10 := by
  have ha := hAI r hr
  have hs : (9/10 : ℝ) ≤ (A r)^2 := by nlinarith [ha.1]
  have hsq : 0 < (A r)^2 := by linarith
  have hav := radialAverage_unit_square_bounds R A hA hAI r hr
  have hq : radialAverage (fun t => (A t)^2) r/(A r)^2 ≤ (1/10 : ℝ) :=
    (div_le_iff₀ hsq).2 (by linarith [hav.2])
  have he : radialVelocityRatio c A r-radialVelocityRatio d A r=
      (c-d)*(radialAverage (fun t => (A t)^2) r/(A r)^2) := by
    unfold radialVelocityRatio
    ring
  rw [he,abs_mul,abs_of_nonneg (div_nonneg hav.1 hsq.le)]
  have h := mul_le_mul_of_nonneg_left hq (abs_nonneg (c-d))
  linarith

theorem radialAmplitudePotential_parameter_difference (c d b e R : ℝ)
    (hc : c ∈ Icc (599/100 : ℝ) 6) (hd : d ∈ Icc (599/100 : ℝ) 6)
    (hR : R^2 ≤ 11) (A : ℝ → ℝ) (hA : Continuous A)
    (hAI : ∀ t ∈ Icc 0 R, A t ∈ Icc (999/1000 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc 0 R) :
    |radialAmplitudePotential c b A r-radialAmplitudePotential d e A r| ≤ |b-e|+|c-d| := by
  have hcρ := radialVelocityRatio_bounds c R hc A hA hAI r hr
  have hdρ := radialVelocityRatio_bounds d R hd A hA hAI r hr
  have hdiff := radialVelocityRatio_parameter_difference c d R A hA hAI r hr
  have hs : |(radialVelocityRatio d A r)^2-(radialVelocityRatio c A r)^2| ≤
      (102/1000 : ℝ)*|c-d| := by
    rw [sq_sub_sq,abs_mul,abs_sub_comm,
      abs_of_nonneg (by linarith [hcρ.1,hdρ.1] : 0 ≤ radialVelocityRatio d A r+radialVelocityRatio c A r)]
    have h := mul_le_mul hdiff (by linarith [hcρ.2,hdρ.2] :
      radialVelocityRatio d A r+radialVelocityRatio c A r ≤ (102/100 : ℝ))
      (by linarith [hcρ.1,hdρ.1]) (by positivity : 0 ≤ |c-d|/10)
    linarith
  have hrR : r^2 ≤ 11 := ((sq_le_sq₀ hr.1 (hr.1.trans hr.2)).2 hr.2).trans hR
  have hp : |r^2/4*((radialVelocityRatio d A r)^2-(radialVelocityRatio c A r)^2)| ≤ |c-d| := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ r^2/4)]
    have h := mul_le_mul (by linarith : r^2/4 ≤ (11/4 : ℝ)) hs
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 11/4)
    nlinarith [abs_nonneg (c-d)]
  have he : radialAmplitudePotential c b A r-radialAmplitudePotential d e A r=
      (b-e)+r^2/4*((radialVelocityRatio d A r)^2-(radialVelocityRatio c A r)^2) := by
    unfold radialAmplitudePotential
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hp)

end DefocusingNLS

end OAI
