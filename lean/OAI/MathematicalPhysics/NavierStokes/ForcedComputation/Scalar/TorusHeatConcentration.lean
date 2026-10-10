import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatMass
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlanePeriodicBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Quantitative concentration of the actual torus heat kernel near the lattice. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter MeasureTheory
open scoped Topology NNReal

def torusHeatTail (d t : ℝ) : ℝ :=
  (8 + 8 * t⁻¹) * Real.exp (-(d^2 / (4*t)))

theorem torusHeatTail_nonneg {t : ℝ} (ht : 0 < t) (d : ℝ) :
    0 ≤ torusHeatTail d t := by unfold torusHeatTail; positivity

theorem torusHeatKernel_le_tail {t d : ℝ} (ht : 0 < t) (x : Plane)
    (hx : d^2 ≤ torusDistanceSq x) : torusHeatKernel t x ≤ torusHeatTail d t := by
  have hq : 1 / (4 * Real.pi * t) ≤ t⁻¹ := by
    rw [one_div, inv_le_inv₀ (by positivity) ht]
    nlinarith [Real.pi_gt_three]
  have hs : Real.sqrt (1 / (4 * Real.pi * t)) ^ 2 = 1 / (4 * Real.pi * t) :=
    Real.sq_sqrt (by positivity)
  have hc : 4 * (1 + Real.sqrt (1 / (4 * Real.pi * t)))^2 ≤ 8 + 8 * t⁻¹ := by
    nlinarith [sq_nonneg (Real.sqrt (1 / (4 * Real.pi * t)) - 1)]
  have he : Real.exp (-(torusDistanceSq x) / (4*t)) ≤ Real.exp (-(d^2 / (4*t))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg ((div_le_div_iff_of_pos_right (by positivity)).mpr hx)
  exact (torusHeatKernel_gaussian ht x).trans
    (mul_le_mul hc he (Real.exp_pos _).le (by positivity))

theorem torusHeatTail_tendsto {d : ℝ} (hd : 0 < d) :
    Tendsto (torusHeatTail d) (𝓝[>] 0) (𝓝 0) := by
  let b := d^2 / 4
  have hb : 0 < b := by dsimp [b]; positivity
  have h₀ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb).comp
    tendsto_inv_nhdsGT_zero
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb).comp
    tendsto_inv_nhdsGT_zero
  have h := (h₀.const_mul 8).add (h₁.const_mul 8)
  simp only [Function.comp_def, Real.rpow_zero, Real.rpow_one, one_mul,
    mul_zero, add_zero] at h
  convert h using 1
  funext t
  dsimp [torusHeatTail, b]
  rw [show -(d^2 / (4*t)) = -(d^2 / 4) * t⁻¹ by ring]
  ring

theorem torusHeatEvolution_error_estimate {g : Plane → ℝ} {K : ℝ≥0} {B d t : ℝ}
    (hg : LipschitzWith K g) (hp : PlanePeriodic g) (hB : ∀ x, |g x| ≤ B)
    (hd : 0 < d) (ht : 0 < t) (x : Plane) :
    |torusHeatEvolution g t x - g x| ≤ K * d + 2 * B * torusHeatTail d t := by
  have hB₀ : 0 ≤ B := (abs_nonneg (g 0)).trans (hB 0)
  have hK : Continuous (fun y : Plane => torusHeatKernel t (x-y)) :=
    (torusHeatKernel_continuous ht).comp (continuous_const.sub continuous_id)
  have hi₁ : IntegrableOn (fun y : Plane => torusHeatKernel t (x-y) * g y)
      (Icc (0 : Plane) (fun _ => 1)) := (hK.mul hg.continuous).integrableOn_Icc
  have hi₂ : IntegrableOn (fun y : Plane => torusHeatKernel t (x-y) * g x)
      (Icc (0 : Plane) (fun _ => 1)) := (hK.mul continuous_const).integrableOn_Icc
  have he : torusHeatEvolution g t x - g x =
      ∫ y in Icc (0 : Plane) (fun _ => 1), torusHeatKernel t (x-y) * (g y - g x) := by
    rw [torusHeatEvolution, ite_eq_right (not_le.mpr ht)]
    simp_rw [mul_sub]
    rw [integral_sub hi₁ hi₂, integral_mul_const, torusHeatKernel_integral ht, one_mul]
  rw [he, ← Real.norm_eq_abs]
  have hi : IntegrableOn (fun y : Plane => K*d*torusHeatKernel t (x-y) +
      2*B*torusHeatTail d t) (Icc (0 : Plane) (fun _ => 1)) :=
    ((continuous_const.mul hK).add continuous_const).integrableOn_Icc
  calc
    _ ≤ ∫ y in Icc (0 : Plane) (fun _ => 1),
        K * d * torusHeatKernel t (x-y) + 2 * B * torusHeatTail d t := by
      apply norm_integral_le_of_norm_le hi
      exact ae_of_all _ fun y => by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (torusHeatKernel_nonneg ht _),
          Real.norm_eq_abs]
        by_cases hnear : torusNorm (x-y) ≤ d
        · have hdiff := planePeriodic_norm_sub_le_torus hg hp x y
          rw [Real.norm_eq_abs, abs_sub_comm] at hdiff
          have hsmall : |g y - g x| ≤ K*d :=
            hdiff.trans (mul_le_mul_of_nonneg_left hnear K.coe_nonneg)
          calc
            _ ≤ torusHeatKernel t (x-y) * ((K : ℝ)*d) :=
              mul_le_mul_of_nonneg_left hsmall (torusHeatKernel_nonneg ht _)
            _ = (K : ℝ)*d*torusHeatKernel t (x-y) := by ring
            _ ≤ _ := le_add_of_nonneg_right (by
              exact mul_nonneg (by positivity) (torusHeatTail_nonneg ht d))
        · have hdist : d^2 ≤ torusDistanceSq (x-y) := by
            rw [← torusNorm_sq]
            nlinarith [lt_of_not_ge hnear, torusNorm_nonneg (x-y)]
          have hdiff : |g y - g x| ≤ 2*B := (abs_sub _ _).trans (by linarith [hB y, hB x])
          have hbound := torusHeatKernel_le_tail ht (x-y) hdist
          calc
            _ ≤ torusHeatKernel t (x-y) * (2*B) :=
              mul_le_mul_of_nonneg_left hdiff (torusHeatKernel_nonneg ht _)
            _ = 2*B*torusHeatKernel t (x-y) := by ring
            _ ≤ 2*B*torusHeatTail d t :=
              mul_le_mul_of_nonneg_left hbound (by positivity)
            _ ≤ _ := le_add_of_nonneg_left
              (mul_nonneg (mul_nonneg K.coe_nonneg hd.le) (torusHeatKernel_nonneg ht _))
    _ = K*d + 2*B*torusHeatTail d t := by
      have hia : IntegrableOn (fun y : Plane => (K : ℝ)*d*torusHeatKernel t (x-y))
          (Icc (0 : Plane) (fun _ => 1)) := (continuous_const.mul hK).integrableOn_Icc
      rw [integral_add (f := fun y : Plane => (K : ℝ)*d*torusHeatKernel t (x-y))
        (g := fun _ : Plane => 2*B*torusHeatTail d t) hia continuous_const.integrableOn_Icc,
        integral_const_mul, torusHeatKernel_integral ht]
      have hvol : volume.real (Icc (0 : Plane) (fun _ => 1)) = 1 := by
        rw [Measure.real, Real.volume_Icc_pi_toReal (a := (0 : Plane))
          (b := fun _ => 1) (fun _ => zero_le_one)]
        simp
      rw [setIntegral_const, hvol, one_smul, mul_one]

theorem torusHeatEvolution_tendsto_uniformly {g : Plane → ℝ}
    (hg : ContDiff ℝ 1 g) (hp : PlanePeriodic g) :
    TendstoUniformly (torusHeatEvolution g) g (𝓝[>] 0) := by
  obtain ⟨K, hK⟩ := planePeriodic_lipschitz hg hp
  obtain ⟨B, _, hB⟩ := planePeriodic_bound hg.continuous hp
  have hB' (x : Plane) : |g x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let d := ε / (2 * ((K : ℝ) + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hsmall : (K : ℝ) * d < ε / 2 := by
    have he : 2 * ((K : ℝ) + 1) * d = ε := by
      dsimp [d]
      field_simp
    nlinarith [K.coe_nonneg]
  have ht := (torusHeatTail_tendsto hd).const_mul (2*B)
  simp only [mul_zero] at ht
  have ht' := (tendsto_order.1 ht).2 (ε/2) (by linarith)
  filter_upwards [self_mem_nhdsWithin, ht'] with t ht₀ htail x
  have he := torusHeatEvolution_error_estimate hK hp hB' hd ht₀ x
  have hlt : |torusHeatEvolution g t x - g x| < ε := by linarith
  simpa only [Real.dist_eq, abs_sub_comm] using hlt

end ForcedComputation.VelocityDetector

end

end OAI
