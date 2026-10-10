import Mathlib
import OAI.Probability.SphericalField.Gibbs.Tilting

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
section GibbsConvex
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_log_partition_deriv {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    HasDerivAt (fun u => Real.log (tiltPartition μ v u)) (tiltMean μ v v t) t := by
  exact (tilt_partition_deriv μ hv hC hvC t).log (tilt_partition_pos μ hv hC hvC t).ne'

lemma tilt_variance_eq {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    tiltMean μ v (fun x => v x * v x) t - tiltMean μ v v t * tiltMean μ v v t =
      variance v (tiltLaw μ v t) := by
  have := tilt_law_probability μ hv hC hvC t
  have hLp : MemLp v 2 (tiltLaw μ v t) := memLp_of_bounded
    (ae_of_all _ fun x => abs_le.mp (hvC x)) hv.aestronglyMeasurable 2
  rw [variance_eq_sub hLp]
  simp_rw [tilt_law_integral μ hv hC hvC t]
  simp only [pow_two]
  rfl

lemma tilt_mean_potential_monotone {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) : Monotone (tiltMean μ v v) := by
  apply monotone_of_hasDerivAt_nonneg (tilt_mean_deriv μ hv hv hC hC hvC hvC)
  intro t
  change 0 ≤ tiltMean μ v (fun x => v x*v x) t - tiltMean μ v v t*tiltMean μ v v t
  rw [tilt_variance_eq μ hv hC hvC]
  exact variance_nonneg _ _

lemma tilt_log_partition_convex {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) :
    ConvexOn ℝ Set.univ (fun t => Real.log (tiltPartition μ v t)) := by
  have hd := tilt_log_partition_deriv μ hv hC hvC
  apply Monotone.convexOn_univ_of_deriv (fun t => (hd t).differentiableAt)
  have he : deriv (fun t => Real.log (tiltPartition μ v t)) = tiltMean μ v v :=
    funext fun t => (hd t).deriv
  rw [he]
  exact tilt_mean_potential_monotone μ hv hC hvC

end GibbsConvex

lemma convex_contact_derivative_bound {f A : ℝ → ℝ} {u s d dA C : ℝ}
    (hs : 0 < s) (hf : ConvexOn ℝ Set.univ f) (hd : HasDerivAt f d u)
    (hp : A (u+s)-A u-s*dA ≤ C*s^2)
    (hm : A (u-s)-A u+s*dA ≤ C*s^2) :
    |d-dA| ≤ C*s + (|f (u+s)-A (u+s)| + 2*|f u-A u| + |f (u-s)-A (u-s)|)/s := by
  have hu := hf.le_slope_of_hasDerivAt (Set.mem_univ u) (Set.mem_univ (u+s))
    (by linarith : u < u+s) hd
  have hl := hf.slope_le_of_hasDerivAt (Set.mem_univ (u-s)) (Set.mem_univ u)
    (by linarith : u-s < u) hd
  simp only [slope_def_field] at hu hl
  have he1 : u+s-u = s := by ring
  have he2 : u-(u-s) = s := by ring
  rw [he1,le_div_iff₀ hs] at hu
  rw [he2,div_le_iff₀ hs] at hl
  apply (abs_le).mpr
  constructor
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    rw [neg_mul,add_mul,div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (u-s)-A (u-s)),neg_abs_le (f u-A u),
      abs_nonneg (f (u+s)-A (u+s)),abs_nonneg (f u-A u)]
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    rw [add_mul,div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (u+s)-A (u+s)),neg_abs_le (f u-A u),
      abs_nonneg (f (u-s)-A (u-s)),abs_nonneg (f u-A u)]

end SphericalPerceptron
end
end

end OAI
