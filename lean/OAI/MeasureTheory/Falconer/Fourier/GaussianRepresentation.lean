import OAI.MeasureTheory.Falconer.Graphs.Energy
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem inverse_power_gaussian_integral {d u k : ℝ}
    (hd : 0 < d) (hu : 0 < u) (hk : 0 < k) :
    d^(-u) = k^(u/2) / Real.Gamma (u/2) *
      ∫ a : ℝ in Ioi 0, a^(u/2-1) * Real.exp (-(k*a*d^2)) := by
  have hg : 0 < Real.Gamma (u/2) := Real.Gamma_pos_of_pos (by positivity)
  have hdu : 0 < d^u := Real.rpow_pos_of_pos hd _
  have hku : 0 < k^(u/2) := Real.rpow_pos_of_pos hk _
  have hp : (d^2)^(u/2) = d^u := by
    rw [← Real.rpow_natCast_mul hd.le]
    congr 1
    ring
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by positivity : 0 < u/2) (mul_pos hk (sq_pos_of_pos hd))
  have he : (fun a : ℝ => a^(u/2-1)*Real.exp (-(k*a*d^2))) =
      (fun a : ℝ => a^(u/2-1)*Real.exp (-((k*d^2)*a))) := by
    funext a
    congr 2
    ring
  rw [he,hi,Real.div_rpow (by norm_num) (mul_nonneg hk.le (sq_nonneg d)),
    Real.one_rpow,Real.mul_rpow hk.le (sq_nonneg d),hp,Real.rpow_neg hd.le]
  field_simp [hg.ne', hdu.ne', hku.ne']

theorem source_inverse_power_gaussian_integral {d u : ℝ} (hd : 0 < d) (hu : 0 < u) :
    d^(-u) = Real.pi^(u/2) / Real.Gamma (u/2) *
      ∫ a : ℝ in Ioi 0, a^(u/2-1) * Real.exp (-(Real.pi*a*d^2)) :=
  inverse_power_gaussian_integral hd hu Real.pi_pos

theorem gaussian_mixture_integrable {d u k : ℝ}
    (hd : 0 < d) (hu : 0 < u) (hk : 0 < k) :
    IntegrableOn (fun a : ℝ => a^(u/2-1)*Real.exp (-(k*a*d^2))) (Ioi 0) volume := by
  by_contra h
  have hi := inverse_power_gaussian_integral hd hu hk
  rw [integral_undef h,mul_zero] at hi
  exact (Real.rpow_pos_of_pos hd (-u)).ne' hi

theorem source_riesz_kernel_gaussian_mixture (x y : Plane) (hxy : x ≠ y)
    {u : ℝ} (hu : 0 < u) :
    (edist x y)^(-u) =
      ENNReal.ofReal (Real.pi^(u/2) / Real.Gamma (u/2)) *
        ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal
          (a^(u/2-1)*Real.exp (-(Real.pi*a*(dist x y)^2))) := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hi := gaussian_mixture_integrable hd hu Real.pi_pos
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun a : ℝ => a^(u/2-1)*Real.exp (-(Real.pi*a*(dist x y)^2))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.exp_pos _).le
  rw [edist_dist,ENNReal.ofReal_rpow_of_pos hd,source_inverse_power_gaussian_integral hd hu,
    ENNReal.ofReal_mul (by positivity),ofReal_integral_eq_lintegral_ofReal hi hn]

noncomputable def gaussianQuadratic (μ : Measure Plane) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : Plane × Plane, ENNReal.ofReal (Real.exp (-(Real.pi*a*(dist z.1 z.2)^2))) ∂μ.prod μ

theorem rieszEnergy_eq_prod (μ : Measure Plane) [SFinite μ] (u : ℝ) :
    rieszEnergy μ u = ∫⁻ z : Plane × Plane, (edist z.1 z.2)^(-u) ∂μ.prod μ := by
  unfold rieszEnergy rieszPotential
  exact lintegral_lintegral (by fun_prop)

theorem gaussianQuadratic_le_mass_sq (μ : Measure Plane) [SFinite μ] {a : ℝ} (ha : 0 ≤ a) :
    gaussianQuadratic μ a ≤ (μ univ)^2 := by
  calc
    gaussianQuadratic μ a ≤ ∫⁻ _ : Plane × Plane, (1 : ℝ≥0∞) ∂μ.prod μ := by
      apply lintegral_mono
      intro z
      have he : Real.exp (-(Real.pi*a*(dist z.1 z.2)^2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr
          (mul_nonneg (mul_nonneg Real.pi_pos.le ha) (sq_nonneg _)))
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he
    _ = _ := by simp [Measure.prod_apply, pow_two]

theorem rieszEnergy_gaussian_mixture (μ : Measure Plane) [SFinite μ]
    [NullSingletonClass μ] {u : ℝ} (hu : 0 < u) :
    rieszEnergy μ u = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
      ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) * gaussianQuadratic μ a := by
  let F : ℝ → Plane × Plane → ℝ≥0∞ := fun a z =>
    ENNReal.ofReal (a^(u/2-1)) *
      ENNReal.ofReal (Real.exp (-(Real.pi*a*(dist z.1 z.2)^2)))
  have hdiag : ∀ᵐ z : Plane × Plane ∂μ.prod μ, z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (p := fun z : Plane × Plane => z.1 ≠ z.2)
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Filter.Eventually.of_forall (fun x => by rw [ae_iff]; simp)
  rw [rieszEnergy_eq_prod]
  calc
    _ = ∫⁻ z : Plane × Plane, ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        (∫⁻ a : ℝ in Ioi 0, F a z) ∂μ.prod μ := by
      apply lintegral_congr_ae
      filter_upwards [hdiag] with z hz
      rw [source_riesz_kernel_gaussian_mixture z.1 z.2 hz hu]
      congr 1
      apply lintegral_congr
      intro a
      exact ENNReal.ofReal_mul' (Real.exp_pos _).le
    _ = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ z : Plane × Plane, (∫⁻ a : ℝ in Ioi 0, F a z) ∂μ.prod μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ a : ℝ in Ioi 0, ∫⁻ z : Plane × Plane, F a z ∂μ.prod μ := by
      congr 1
      apply lintegral_lintegral_swap
      have hm : Measurable (fun z : (Plane × Plane) × ℝ => F z.2 z.1) := by
        dsimp [F]
        fun_prop
      exact hm.aemeasurable
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro a
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end PlanarFalconer

end OAI
