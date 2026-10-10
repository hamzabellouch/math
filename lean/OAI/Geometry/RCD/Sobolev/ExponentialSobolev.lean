import OAI.Geometry.RCD.Heat.RenyiFisherBounds
import OAI.Analysis.RCDHeat.GeodesicCauchy

namespace OAI

/-! # Actual positive Sobolev densities with a controlled logarithm -/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
 theorem exponential_sobolev (p : X) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hi : Integrable (fun x => Real.exp (-(2*a)*dist p x)) μ) :
    ∃ ρ : SobolevSpace μ hQ,
      SobolevSpace.toLp μ hQ ρ =ᵐ[μ] fun x => c*Real.exp (-a*dist p x) := by
  let E := exp_neg_dist_memLp_two μ p a hi
  let u := c • E.toLp (fun x => Real.exp (-a*dist p x))
  have hu : (u : X → ℝ) =ᵐ[μ] fun x => c*Real.exp (-a*dist p x) := by
    filter_upwards [Lp.coeFn_smul c (E.toLp _),E.coeFn_toLp] with x hx he
    simpa only [u,Pi.smul_apply,smul_eq_mul,he] using hx
  have hg := lipschitzWith_const_mul_real (exp_neg_dist_lipschitz p ha) c
  have hm := (exp_neg_dist_slopeMajorant μ p ha hi).const_mul μ hc.le
  have he := energyLp_le_of_lipschitz_majorant μ hg hu hm
  have hfin : energyLp μ u ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top he
  exact ⟨⟨u,hfin⟩,hu⟩

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
 theorem exponential_log_lipschitz (p : X) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    LipschitzWith ⟨a,ha⟩ (fun x => Real.log (c*Real.exp (-a*dist p x))) := by
  have he : (fun x => Real.log (c*Real.exp (-a*dist p x))) =
      fun x => Real.log c-a*dist p x := by
    funext x
    rw [Real.log_mul hc.ne' (Real.exp_ne_zero _),Real.log_exp]
    ring
  rw [he]
  have hn : ‖-a‖₊*1=(⟨a,ha⟩:ℝ≥0) := by
    ext
    change |-a| * 1=a
    rw [abs_neg,abs_of_nonneg ha,mul_one]
  have hh := (LipschitzWith.const (Real.log c)).add
    (lipschitzWith_const_mul_real (LipschitzWith.dist_right p) (-a))
  rw [zero_add,hn] at hh
  simpa only [neg_mul,sub_eq_add_neg] using hh

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
 theorem exponential_bounded (p : X) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (x : X) :
    c*Real.exp (-a*dist p x) ≤ c := by
  have he : Real.exp (-a*dist p x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) dist_nonneg
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he hc

end RegularPointCoordinates

end

end OAI
