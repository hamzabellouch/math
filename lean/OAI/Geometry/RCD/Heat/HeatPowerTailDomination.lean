import OAI.Geometry.RCD.Heat.ExponentialHeatPower

namespace OAI

/-! # Heat power integrability from an exponential upper bound -/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem heat_power_integrable_of_exponential_bound (p : X) {V B a c q t : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (ha : 2*(B+1) ≤ a)
    (hq0 : 1/2 ≤ q) (hq1 : q ≤ 1)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf : 0 ≤ f)
    (hbound : ∀ᵐ x ∂μ, |f x| ≤ c*Real.exp (-a*dist p x))
    (ht : 0 ≤ t) : Integrable (fun x => (heatAt μ hQ t f x)^q) μ := by
  have hprod : 0 ≤ (2*q-1)*(B+1) := mul_nonneg (by linarith) (by linarith)
  have hr : B < q*(2*(B+1)) := by nlinarith
  have he : B < 2*a-(2-q)*(2*(B+1)) := by nlinarith
  have hi := (integrable_exp_neg_dist_of_volume μ p hV hB he hvol).const_mul (c^2)
  have hfi : Integrable (fun x => Real.exp (((2-q)*(2*(B+1)))*dist p x)*(f x)^2) μ := by
    apply hi.mono'
      (((by fun_prop : Continuous (fun x : X => Real.exp (((2-q)*(2*(B+1)))*dist p x))).aestronglyMeasurable).mul
        ((Lp.aestronglyMeasurable f).pow 2))
    filter_upwards [hbound] with x hx
    change |Real.exp (((2-q)*(2*(B+1)))*dist p x)*(f x)^2| ≤ _
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    have hs : (f x)^2 ≤ (c*Real.exp (-a*dist p x))^2 := by
      nlinarith [abs_nonneg (f x),sq_abs (f x)]
    calc
      _ ≤ Real.exp (((2-q)*(2*(B+1)))*dist p x)*(c*Real.exp (-a*dist p x))^2 :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = _ := weighted_exponential_square _ _ _ _
  have hp := heat_power_integrable_of_exponential_energy μ hQ p hV hB (by positivity)
    (by linarith) (by linarith) hr hvol f ht hfi
  apply hp.congr
  filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf)] with x hx
  rw [abs_of_nonneg hx]

end RegularPointCoordinates

end

end OAI
