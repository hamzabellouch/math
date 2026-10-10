import OAI.Geometry.RCD.Heat.HeatPowerIntegrability

namespace OAI

/-! # Power entropy of the heat evolution of the constructed exponential density -/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates

 theorem weighted_exponential_square (a b c d : ℝ) :
    Real.exp (b*d)*(c*Real.exp (-a*d))^2=c^2*Real.exp (-(2*a-b)*d) := by
  calc
    _ = c^2*(Real.exp (b*d)*Real.exp (2*(-a*d))) := by
      rw [mul_pow,←Real.exp_nat_mul]
      ring_nf
    _ = _ := by rw [←Real.exp_add]; congr 2; ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem exponential_heat_power_integrable (p : X) {V B a c q t : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (ha : 2*(B+1) ≤ a) (hc : 0 ≤ c)
    (hq0 : 1/2 ≤ q) (hq1 : q ≤ 1)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hrep : f =ᵐ[μ] fun x => c*Real.exp (-a*dist p x))
    (ht : 0 ≤ t) : Integrable (fun x => (heatAt μ hQ t f x)^q) μ := by
  have hprod : 0 ≤ (2*q-1)*(B+1) := mul_nonneg (by linarith) (by linarith)
  have hr : B < q*(2*(B+1)) := by nlinarith
  have he : B < 2*a-(2-q)*(2*(B+1)) := by nlinarith
  have hi := (integrable_exp_neg_dist_of_volume μ p hV hB he hvol).const_mul (c^2)
  have hfi : Integrable (fun x => Real.exp (((2-q)*(2*(B+1)))*dist p x)*(f x)^2) μ := by
    apply hi.congr
    filter_upwards [hrep] with x hx
    rw [hx,weighted_exponential_square]
  have hp := heat_power_integrable_of_exponential_energy μ hQ p hV hB (by positivity)
    (by linarith) (by linarith) hr hvol f ht hfi
  have hf : 0 ≤ f := (Lp.coeFn_nonneg _).mp
    (hrep.mono fun x hx => hx ▸ mul_nonneg hc (Real.exp_pos _).le)
  apply hp.congr
  filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf)] with x hx
  rw [abs_of_nonneg hx]

end RegularPointCoordinates

end

end OAI
