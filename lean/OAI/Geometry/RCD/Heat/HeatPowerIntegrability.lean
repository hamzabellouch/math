import OAI.Geometry.RCD.Heat.HeatExponentialEnergy

namespace OAI

/-! # Finite power entropy of heat flows with exponential energy tails -/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates

 theorem power_exponential_energy_bound {r q a : ℝ} (hr : 0 ≤ r)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2) :
    r^q ≤ Real.exp ((2-q)*a)*r^2+Real.exp (-q*a) := by
  by_cases hsmall : r ≤ Real.exp (-a)
  · have hh := Real.rpow_le_rpow hr hsmall hq0
    rw [←Real.exp_mul] at hh
    have he : -a*q= -q*a := by ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
  · have hr0 : 0 < r := (Real.exp_pos (-a)).trans (lt_of_not_ge hsmall)
    calc
      _ = r^2*r^(q-2) := by
        rw [←Real.rpow_two,←Real.rpow_add hr0]
        congr 1
        ring
      _ ≤ r^2*(Real.exp (-a))^(q-2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (le_of_not_ge hsmall) (sub_nonpos.mpr hq2))
        (sq_nonneg _)
      _ = Real.exp ((2-q)*a)*r^2 := by
        rw [←Real.exp_mul]
        have he : -a*(q-2)=(2-q)*a := by ring
        rw [he,mul_comm]
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

 theorem heat_power_integrable_of_exponential_energy (p : X) {V B a q t : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (ha : 0 ≤ a) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hrate : B < q*a)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (ht : 0 ≤ t)
    (hfi : Integrable (fun x => Real.exp (((2-q)*a)*dist p x)*(f x)^2) μ) :
    Integrable (fun x => |heatAt μ hQ t f x|^q) μ := by
  have henergy := (heat_exponential_energy μ hQ f p (mul_nonneg (sub_nonneg.mpr hq2) ha) ht hfi).1
  have hneg := integrable_exp_neg_dist_of_volume μ p hV hB hrate hvol
  apply (henergy.add hneg).mono_nonneg
    (((Lp.stronglyMeasurable (heatAt μ hQ t f)).measurable.abs.pow_const q).aestronglyMeasurable)
  · exact .of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _
  · filter_upwards with x
    have h := power_exponential_energy_bound (a := a*dist p x) (abs_nonneg (heatAt μ hQ t f x)) hq0 hq2
    simpa only [sq_abs,mul_assoc,neg_mul,Pi.add_apply] using h

end RegularPointCoordinates

end

end OAI
