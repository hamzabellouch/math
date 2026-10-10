import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatSmoothing
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatOperator
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetCurves
import Mathlib.Topology.UniformSpace.UniformApproximation

namespace OAI

/-! The Gaussian first moment and uniform initial continuity for bounded Lipschitz data. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open ShearFlows MeasureTheory Set Filter
open scoped Topology NNReal ContDiff

theorem kernel_coordinate_moment {t : ℝ} (ht : 0 < t) (x : Plane) (j : Fin 2) :
    kernel t x * |x j| = (2*t) * |kernelDerivative t j x| := by
  simp only [kernelDerivative, abs_mul, abs_neg, abs_div,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ht),
    abs_of_nonneg (kernel_nonneg t x)]
  field_simp [ht.ne']

theorem kernel_coordinate_integrable {t : ℝ} (ht : 0 < t) (j : Fin 2) :
    Integrable (fun x : Plane => kernel t x * |x j|) := by
  simpa only [kernel_coordinate_moment ht] using
    ((kernelDerivative_integrable ht j).abs.const_mul (2*t))

theorem kernel_coordinate_integral_le {t : ℝ} (ht : 0 < t) (j : Fin 2) :
    (∫ x : Plane, kernel t x * |x j|) ≤ 4 * Real.sqrt t := by
  simp_rw [kernel_coordinate_moment ht]
  rw [integral_const_mul]
  have hdiv : t / Real.sqrt t = Real.sqrt t := by
    apply (div_eq_iff (Real.sqrt_pos.mpr ht).ne').mpr
    nlinarith [Real.sq_sqrt ht.le]
  calc
    _ ≤ (2*t) * (2 / Real.sqrt t) := mul_le_mul_of_nonneg_left
      (kernelDerivative_abs_integral_le ht j) (by positivity)
    _ = 4 * (t / Real.sqrt t) := by ring
    _ = _ := by rw [hdiv]

private theorem plane_norm_le_coordinate_sum (x : Plane) : ‖x‖ ≤ |x 0|+|x 1| := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
  intro j
  fin_cases j <;> simp only [Real.norm_eq_abs]
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · exact le_add_of_nonneg_left (abs_nonneg _)

theorem kernel_norm_moment_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Plane => kernel t x * ‖x‖) := by
  apply ((kernel_coordinate_integrable ht 0).add
    (kernel_coordinate_integrable ht 1)).mono'
  · exact ((kernel_smooth t).continuous.mul continuous_norm).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kernel_nonneg t x) (norm_nonneg x))]
      simpa only [mul_add, Pi.add_apply] using mul_le_mul_of_nonneg_left
        (plane_norm_le_coordinate_sum x) (kernel_nonneg t x)

theorem kernel_norm_moment_le {t : ℝ} (ht : 0 < t) :
    (∫ x : Plane, kernel t x * ‖x‖) ≤ 8 * Real.sqrt t := by
  calc
    _ ≤ ∫ x : Plane, kernel t x * |x 0| + kernel t x * |x 1| := by
      apply integral_mono (kernel_norm_moment_integrable ht)
        ((kernel_coordinate_integrable ht 0).add (kernel_coordinate_integrable ht 1))
      intro x
      simpa only [mul_add, Pi.add_apply] using mul_le_mul_of_nonneg_left
        (plane_norm_le_coordinate_sum x) (kernel_nonneg t x)
    _ = (∫ x : Plane, kernel t x * |x 0|) + ∫ x : Plane, kernel t x * |x 1| :=
      integral_add (kernel_coordinate_integrable ht 0) (kernel_coordinate_integrable ht 1)
    _ ≤ _ := by linarith [kernel_coordinate_integral_le ht 0, kernel_coordinate_integral_le ht 1]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def evolution (f : Plane → F) (t : ℝ) (x : Plane) : F :=
  if t ≤ 0 then f x else heatConvolution F t f x

theorem norm_evolution_sub_le {f : Plane → F} {L : ℝ≥0} (hL : LipschitzWith L f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) {t : ℝ} (ht : 0 < t) (x : Plane) :
    ‖evolution F f t x - f x‖ ≤ 8 * L * Real.sqrt t := by
  have hi := BoundedKernel.integrand_integrable Plane F volume (kernel t) f
    (kernel_integrable ht) hL.continuous C hC x
  have hc := (kernel_integrable ht).smul_const (f x)
  have he : evolution F f t x - f x =
      ∫ y : Plane, kernel t y • (f (x-y)-f x) := by
    rw [evolution, ite_eq_right (not_le.mpr ht), heatConvolution_eq]
    unfold BoundedKernel.convolve
    simp_rw [smul_sub]
    rw [integral_sub hi hc, integral_smul_const, kernel_integral ht, one_smul]
  have hm : Integrable (fun y : Plane => kernel t y • (f (x-y)-f x)) := by
    convert! hi.sub hc using 1
    funext y
    exact smul_sub _ _ _
  rw [he]
  calc
    _ ≤ ∫ y : Plane, ‖kernel t y • (f (x-y)-f x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : Plane, (L : ℝ) * (kernel t y * ‖y‖) := by
      apply integral_mono hm.norm ((kernel_norm_moment_integrable ht).const_mul (L : ℝ))
      intro y
      have hd := hL.norm_sub_le (x-y) x
      have hy : x-y-x = -y := by abel
      rw [hy, norm_neg] at hd
      change ‖kernel t y • (f (x-y)-f x)‖ ≤ (L : ℝ) * (kernel t y * ‖y‖)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg t y)]
      calc
        _ ≤ kernel t y * ((L : ℝ)*‖y‖) := mul_le_mul_of_nonneg_left hd (kernel_nonneg t y)
        _ = _ := by ring
    _ = (L : ℝ) * ∫ y : Plane, kernel t y * ‖y‖ := integral_const_mul _ _
    _ ≤ (L : ℝ) * (8 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left (kernel_norm_moment_le ht) L.coe_nonneg
    _ = _ := by ring

theorem evolution_tendsto_uniformly {f : Plane → F} {L : ℝ≥0} (hL : LipschitzWith L f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    TendstoUniformly (evolution F f) f (𝓝[>] 0) := by
  have hlim : Tendsto (fun t : ℝ => 8 * (L : ℝ) * Real.sqrt t) (𝓝[>] 0) (𝓝 0) := by
    convert! (show Tendsto (fun t : ℝ => 8 * (L : ℝ) * Real.sqrt t)
      (𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi (0 : ℝ))) (𝓝 (8 * (L : ℝ) * Real.sqrt 0)) from
      (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left inf_le_left |>.const_mul (8 * (L : ℝ))
      ) using 1
    simp only [Real.sqrt_zero, mul_zero]
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [self_mem_nhdsWithin, (tendsto_order.mp hlim).2 ε hε] with t ht hb x
  have h := (norm_evolution_sub_le F hL C hC ht x).trans_lt hb
  simpa only [dist_eq_norm, norm_sub_rev] using h

omit [CompleteSpace F] in
theorem jet_lipschitz (k : ℕ) (J : BoundedSpatialJets.Space Plane F (k+1))
    (i : Fin (k+1)) : LipschitzWith ‖J‖₊ (J.val i.castSucc) := by
  have hd (x : Plane) := BoundedSpatialJets.hasFDerivAt Plane F (k+1) J i x
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hd x).differentiableAt)
  intro x
  have hn : ‖fderiv ℝ (J.val i.castSucc) x‖ ≤ ‖J‖ := by
    rw [(hd x).fderiv, (BoundedSpatialJets.curryMap Plane F i.val).norm_map]
    exact BoundedSpatialJets.norm_jet_le Plane F (k+1) J i.succ x
  exact_mod_cast hn

theorem norm_heatOperator_truncate_sub_le (k : ℕ)
    (J : BoundedSpatialJets.Space Plane F (k+1)) {t : ℝ} (ht : 0 < t) :
    ‖heatOperator F k t ht (BoundedSpatialJets.truncate Plane F k (k+1) (by omega) J) -
      BoundedSpatialJets.truncate Plane F k (k+1) (by omega) J‖ ≤
        8 * ‖J‖ * Real.sqrt t := by
  have htr (i : Fin (k+1)) (x : Plane) :
      (BoundedSpatialJets.truncate Plane F k (k+1) (by omega) J).val i x =
        J.val i.castSucc x := by
    change iteratedFDeriv ℝ i.val (BoundedSpatialJets.function Plane F (k+1) J) x = _
    exact congrFun (BoundedSpatialJets.iteratedFDeriv_function Plane F (k+1) J i.val (by omega)) x
  apply BoundedSpatialJets.norm_sub_le_of_jets Plane F k _ _ (by positivity)
  intro i x
  rw [heatOperator_jet]
  simp_rw [htr]
  have h := norm_evolution_sub_le (BoundedSpatialJets.Value Plane F i.val)
    (jet_lipschitz F k J i) ‖J‖ (BoundedSpatialJets.norm_jet_le Plane F (k+1) J i.castSucc)
    ht x
  rw [evolution, ite_eq_right (not_le.mpr ht), heatConvolution_eq] at h
  exact h

/-- The heat operator at nonpositive time is the identity. Only strong, applied
continuity at zero is asserted; operator-norm continuity there is unnecessary. -/
def evolutionOperator (k : ℕ) (t : ℝ) :
    BoundedSpatialJets.Space Plane F k →L[ℝ] BoundedSpatialJets.Space Plane F k :=
  if ht : 0 < t then heatOperator F k t ht else ContinuousLinearMap.id ℝ _

theorem evolutionOperator_function (k : ℕ) (t : ℝ)
    (J : BoundedSpatialJets.Space Plane F k) (x : Plane) :
    BoundedSpatialJets.function Plane F k (evolutionOperator F k t J) x =
      evolution F (BoundedSpatialJets.function Plane F k J) t x := by
  by_cases ht : 0 < t
  · rw [evolutionOperator, dite_eq_left ht, evolution, ite_eq_right (not_le.mpr ht),
      heatConvolution_eq]
    exact heatOperator_apply F k t ht J x
  · simp only [evolutionOperator, dite_eq_right ht, ContinuousLinearMap.id_apply,
      evolution, ite_eq_left (not_lt.mp ht)]

theorem evolutionOperator_initial (k : ℕ) :
    evolutionOperator F k 0 = ContinuousLinearMap.id ℝ _ := by
  simp only [evolutionOperator, lt_self_iff_false, ↓reduceDIte]

theorem evolutionOperator_truncate_tendsto (k : ℕ)
    (J : BoundedSpatialJets.Space Plane F (k+1)) :
    Tendsto (fun t : ℝ => evolutionOperator F k t
      (BoundedSpatialJets.truncate Plane F k (k+1) (by omega) J)) (𝓝 0)
        (𝓝 (BoundedSpatialJets.truncate Plane F k (k+1) (by omega) J)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
  · intro t
    by_cases ht : 0 < t
    · rw [evolutionOperator, dite_eq_left ht]
      exact norm_heatOperator_truncate_sub_le F k J ht
    · rw [evolutionOperator, dite_eq_right ht, ContinuousLinearMap.id_apply, sub_self, norm_zero]
      positivity
  · convert! (Real.continuous_sqrt.tendsto (0 : ℝ)).const_mul (8 * ‖J‖) using 1
    simp only [Real.sqrt_zero, mul_zero]

end ForcedComputation.PlaneHeat

end

end OAI
