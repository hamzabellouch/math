import OAI.Geometry.RCD.Sobolev.LipschitzL2PointControl

namespace OAI

/-! # Sharp off-diagonal L² decay for the actual heat semigroup

Optimizing the established Davies exponential weight gives the squared
L² tail with exponent `-d²/(2t)` and the pairing estimate with exponent
`-d²/(4t)`. No heat-kernel or Gaussian premise is used.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heatAt_radial_L2_tail (f : Lp ℝ 2 μ) (p : X) {r R t : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) (hrR : r ≤ R) (ht : 0 < t)
    {S : Set X} (hS : MeasurableSet S) (hfar : ∀ x ∈ S, R ≤ dist p x) :
    (∫ x in S, (heatAt μ hQ t f x)^2 ∂μ) ≤
      Real.exp (-(R-r)^2 / (2*t)) * ‖f‖^2 := by
  let a := (R-r)/t
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hrR) ht.le
  have hi := heatAt_radialWeight_integral μ hQ f p ha R ht.le
  have hweight : Real.exp (a*R) * (∫ x in S, (heatAt μ hQ t f x)^2 ∂μ) =
      ∫ x in S, radialWeight p a R x * (heatAt μ hQ t f x)^2 ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hS
    intro x hx
    change Real.exp (a*R) * (heatAt μ hQ t f x)^2 =
      Real.exp (a * min (dist p x) R) * (heatAt μ hQ t f x)^2
    rw [min_eq_right (hfar x hx)]
  have hle : Real.exp (a*R) * (∫ x in S, (heatAt μ hQ t f x)^2 ∂μ) ≤
      Real.exp (a^2/2*t+a*r) * ‖f‖^2 := by
    rw [hweight]
    exact (setIntegral_le_integral hi.1
      (Eventually.of_forall fun x => mul_nonneg (radialWeight_nonneg p a R x) (sq_nonneg _))).trans
        (heatAt_radialWeight_integral_le μ hQ f p hf ha R ht.le)
  have hdivide : (∫ x in S, (heatAt μ hQ t f x)^2 ∂μ) ≤
      (Real.exp (a^2/2*t+a*r) * ‖f‖^2) / Real.exp (a*R) :=
    (le_div_iff₀ (Real.exp_pos (a*R))).mpr (by simpa only [mul_comm] using hle)
  calc
    _ ≤ (Real.exp (a^2/2*t+a*r) * ‖f‖^2) / Real.exp (a*R) := hdivide
    _ = Real.exp (a^2/2*t+a*r-a*R) * ‖f‖^2 := by rw [Real.exp_sub]; ring
    _ = _ := by
      congr 2
      dsimp only [a]
      field_simp
      ring

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
theorem integral_mul_sq_le_integral_sq (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ|^2 ≤ (∫ x, (f x)^2 ∂μ) * (∫ x, (g x)^2 ∂μ) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have he : (∫ x, f x * g x ∂μ) = inner ℝ F G := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    change F x = f x at hx
    change G x = g x at hy
    simp only [Real.inner_apply, hx, hy]
  have hF : (∫ x, (f x)^2 ∂μ) = ‖F‖^2 := by
    rw [← integral_sq_Lp μ F]
    exact integral_congr_ae (hf.coeFn_toLp.symm.fun_comp fun a : ℝ => a^2)
  have hG : (∫ x, (g x)^2 ∂μ) = ‖G‖^2 := by
    rw [← integral_sq_Lp μ G]
    exact integral_congr_ae (hg.coeFn_toLp.symm.fun_comp fun a : ℝ => a^2)
  rw [he, hF, hG, ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm F G) 2

theorem heatAt_radial_pairing_sq (f g : Lp ℝ 2 μ) (p : X) {r R t : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (hg : ∀ᵐ x ∂μ, g x ≠ 0 → R ≤ dist p x) (hrR : r ≤ R) (ht : 0 < t) :
    |inner ℝ (heatAt μ hQ t f) g|^2 ≤
      Real.exp (-(R-r)^2 / (2*t)) * ‖f‖^2 * ‖g‖^2 := by
  let S := {x : X | R ≤ dist p x}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have he : inner ℝ (heatAt μ hQ t f) g = ∫ x in S, heatAt μ hQ t f x * g x ∂μ := by
    rw [L2.inner_def, ← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    by_cases h : x ∈ S
    · simp only [indicator_of_mem h, Real.inner_apply, mul_comm]
    · have hzero : g x = 0 := by
        by_contra hn
        exact h (hx hn)
      simp only [indicator_of_notMem h, Real.inner_apply, hzero, mul_zero]
  rw [he]
  have hcs := integral_mul_sq_le_integral_sq (μ.restrict S)
    (heatAt μ hQ t f) g ((Lp.memLp _).mono_measure Measure.restrict_le_self)
      ((Lp.memLp g).mono_measure Measure.restrict_le_self)
  have htail := heatAt_radial_L2_tail μ hQ f p hf hrR ht hS (fun _ hx => hx)
  have hgnorm : (∫ x in S, (g x)^2 ∂μ) ≤ ‖g‖^2 := by
    rw [← integral_sq_Lp μ g]
    exact setIntegral_le_integral (Lp.memLp g).integrable_sq
      (Eventually.of_forall fun x => sq_nonneg (g x))
  exact hcs.trans (mul_le_mul htail hgnorm
    (integral_nonneg fun x => sq_nonneg (g x)) (by positivity))

theorem heatAt_radial_pairing (f g : Lp ℝ 2 μ) (p : X) {r R t : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (hg : ∀ᵐ x ∂μ, g x ≠ 0 → R ≤ dist p x) (hrR : r ≤ R) (ht : 0 < t) :
    |inner ℝ (heatAt μ hQ t f) g| ≤
      Real.exp (-(R-r)^2 / (4*t)) * ‖f‖ * ‖g‖ := by
  have hs := heatAt_radial_pairing_sq μ hQ f g p hf hg hrR ht
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  have hexp : Real.exp (-(R-r)^2 / (4*t)) ^ 2 = Real.exp (-(R-r)^2 / (2*t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    ring
  simpa only [mul_pow, hexp] using hs

end RegularPointCoordinates

end

end OAI
