import OAI.Geometry.RCD.Sobolev.ExponentialSobolev

namespace OAI

/-! # Power and transport moments of an exponential Sobolev density -/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

 theorem exponential_density_power_integrable (p : X) {V B a c s : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (hc : 0 ≤ c) (hrate : B < a*s)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R)) :
    Integrable (fun x => (c*Real.exp (-a*dist p x))^s) μ := by
  have hi := integrable_exp_neg_dist_of_volume μ p hV hB hrate hvol
  convert hi.const_mul (c^s) using 1
  funext x
  rw [Real.mul_rpow hc (Real.exp_pos _).le,←Real.exp_mul]
  congr 2
  ring

 theorem exponential_density_moment_integrable (p : X) {V B a c b : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (hrate : B < a-b)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R)) :
    Integrable (fun x => Real.exp (b*dist p x))
      (μ.withDensity (fun x => ENNReal.ofReal (c*Real.exp (-a*dist p x)))) := by
  have hi := (integrable_exp_neg_dist_of_volume μ p hV hB hrate hvol).const_mul c
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  by_cases hc : 0 ≤ c
  · apply hi.congr
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (mul_nonneg hc (Real.exp_pos _).le),smul_eq_mul]
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    convert (integrable_zero X ℝ μ) using 1
    funext x
    rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hc' (Real.exp_pos _).le)]
    simp

 theorem exponential_density_second_moment (p : X) {V B a c : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (hc : 0 ≤ c) (hrate : B+3 ≤ a)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R)) :
    Integrable (fun x => dist p x^2)
      (μ.withDensity (fun x => ENNReal.ofReal (c*Real.exp (-a*dist p x)))) := by
  have hi := (integrable_dist_pow_mul_exp_of_le μ p (b := a) hV hB hvol 2 (by norm_num; linarith)).const_mul c
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hi.congr
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (mul_nonneg hc (Real.exp_pos _).le),smul_eq_mul]
  ring

end RegularPointCoordinates

end

end OAI
