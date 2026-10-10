import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SuffixDescendants

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set
open scoped ENNReal
section KernelConvolution
variable {V : Type*} [NormedAddCommGroup V]

noncomputable def polynomialKernel (p : ℕ) (z : V) : ℝ := ((1 + ‖z‖)^p)⁻¹

theorem polynomialKernel_pos (p : ℕ) (z : V) : 0 < polynomialKernel p z := by
  unfold polynomialKernel
  positivity

theorem polynomialKernel_le_one (p : ℕ) (z : V) : polynomialKernel p z ≤ 1 := by
  unfold polynomialKernel
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg z]))

theorem continuous_polynomialKernel (p : ℕ) : Continuous (polynomialKernel p : V → ℝ) := by
  unfold polynomialKernel
  apply ((continuous_const.add continuous_norm).pow p).inv₀
  intro z
  change (1 + ‖z‖)^p ≠ 0
  positivity

theorem polynomialKernel_nearby (p : ℕ) (v x y : V) (hxy : dist x y ≤ 1) :
    polynomialKernel p (v-x) ≤ 2^p * polynomialKernel p (v-y) := by
  have hx : 0 < (1 + ‖v-x‖)^p := by positivity
  have hy : 0 < (1 + ‖v-y‖)^p := by positivity
  have htri := norm_add_le (v-x) (x-y)
  rw [sub_add_sub_cancel] at htri
  rw [dist_eq_norm] at hxy
  have hh : 1 + ‖v-y‖ ≤ 2 * (1 + ‖v-x‖) := by
    linarith [norm_nonneg (v-x)]
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + ‖v-y‖) hh p
  rw [mul_pow] at hp
  unfold polynomialKernel
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hx hy]
  simpa only [one_mul] using hp

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem polynomialKernel_integrable {p : ℕ} (hp : Module.finrank ℝ V < p) :
    Integrable (polynomialKernel p : V → ℝ) := by
  have hi := integrable_one_add_norm (E := V) (μ := volume)
    (show (Module.finrank ℝ V : ℝ) < (p : ℝ) by exact_mod_cast hp)
  convert hi using 1
  ext z
  simp [polynomialKernel, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖z‖)]

theorem polynomialKernel_integral_le (ν : Measure V) [IsFiniteMeasure ν]
    {p : ℕ} (hp : Module.finrank ℝ V < p) {A : ℝ} (hA : 0 ≤ A)
    (hball : ∀ x : V, ν (Metric.ball x 1) ≤ ENNReal.ofReal A) (v : V) :
    (∫ x : V, polynomialKernel p (v-x) ∂ν) ≤
      (2^p * A / volume.real (Metric.ball (0 : V) 1)) *
        ∫ z : V, polynomialKernel p z := by
  have hk := (polynomialKernel_integrable (V := V) hp).comp_sub_left v
  let F : V × V → ℝ := {z | dist z.1 z.2 < 1}.indicator
    (fun z => polynomialKernel p (v-z.2))
  have hF : Integrable F (ν.prod volume) := by
    have hh := (integrable_const (μ := ν) (1 : ℝ)).mul_prod hk
    simp only [one_mul] at hh
    exact hh.indicator (measurableSet_lt (by fun_prop) measurable_const)
  have hFx (x : V) : (fun y => F (x,y)) =
      (Metric.ball x 1).indicator (fun y => polynomialKernel p (v-y)) := by
    funext y
    simp [F, Set.indicator, Metric.mem_ball, dist_comm]
  have hFy (y : V) : (fun x => F (x,y)) =
      (Metric.ball y 1).indicator (fun _ => polynomialKernel p (v-y)) := by
    funext x
    simp [F, Set.indicator, Metric.mem_ball]
  have hswap := integral_integral_swap (f := fun x y => F (x,y)) hF
  change (∫ x, ∫ y, F (x,y) ∂volume ∂ν) =
    ∫ y, ∫ x, F (x,y) ∂ν ∂volume at hswap
  simp_rw [hFx, hFy, integral_indicator measurableSet_ball,
    setIntegral_const, smul_eq_mul] at hswap
  have hi : Integrable (fun x : V => ∫ y : V in Metric.ball x 1,
      polynomialKernel p (v-y)) ν := by
    have hh := hF.integral_prod_left
    simpa only [hFx, integral_indicator measurableSet_ball] using hh
  have hlocal (x : V) : volume.real (Metric.ball (0 : V) 1) *
      polynomialKernel p (v-x) ≤
        2^p * ∫ y : V in Metric.ball x 1, polynomialKernel p (v-y) := by
    have hh := integral_mono_of_nonneg
      (μ := volume.restrict (Metric.ball x 1))
      (ae_of_all _ (fun _ => (polynomialKernel_pos p (v-x)).le))
      (hk.integrableOn.const_mul (2^p))
      (show ∀ᵐ y ∂volume.restrict (Metric.ball x 1),
        polynomialKernel p (v-x) ≤ 2^p * polynomialKernel p (v-y) from by
          filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
          exact polynomialKernel_nearby p v x y
            (by have hh : dist x y < 1 := by simpa [Metric.mem_ball, dist_comm] using hy
                exact hh.le))
    simpa only [integral_const, smul_eq_mul,
      integral_const_mul, measureReal_def, Measure.restrict_apply_univ,
      Measure.addHaar_ball_center] using hh
  have hbpos : 0 < volume.real (Metric.ball (0 : V) 1) :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume (0 : V) (by norm_num)))
      measure_ball_lt_top.ne
  have hglobal := integral_mono_of_nonneg
    (ae_of_all ν (fun x => mul_nonneg hbpos.le (polynomialKernel_pos p (v-x)).le))
    (hi.const_mul (2^p)) (ae_of_all ν hlocal)
  rw [integral_const_mul, integral_const_mul, hswap] at hglobal
  have hbound : (∫ y : V, ν.real (Metric.ball y 1) * polynomialKernel p (v-y)) ≤
      A * ∫ z : V, polynomialKernel p z := by
    have hm (y : V) : ν.real (Metric.ball y 1) ≤ A := by
      simpa only [measureReal_def, ENNReal.toReal_ofReal hA] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hball y)
    have hh := integral_mono_of_nonneg
      (ae_of_all volume (fun y => mul_nonneg (measureReal_nonneg)
        (polynomialKernel_pos p (v-y)).le)) (hk.const_mul A)
      (ae_of_all volume (fun y => mul_le_mul_of_nonneg_right (hm y)
        (polynomialKernel_pos p (v-y)).le))
    simpa only [integral_const_mul, integral_sub_left_eq_self] using hh
  have hh := hglobal.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hbpos).mpr
  convert hh using 1 <;> ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in

theorem schwartz_le_polynomialKernel (f : SchwartzMap V ℂ) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : V, ‖f z‖ ≤ C * polynomialKernel p z := by
  let C₀ : ℝ := 2^p * ((Finset.Iic (p,0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) f
  refine ⟨max 1 C₀, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _), ?_⟩
  intro z
  have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (p,0)) le_rfl le_rfl f z
  simp only [norm_iteratedFDeriv_zero] at hh
  have hh' : (1 + ‖z‖)^p * ‖f z‖ ≤ max 1 C₀ := hh.trans (le_max_right _ _)
  unfold polynomialKernel
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < (1 + ‖z‖)^p)]
  simpa only [mul_comm] using hh'

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem polynomialKernel_integrable_finite (ν : Measure V) [IsFiniteMeasure ν]
    (p : ℕ) (v : V) : Integrable (fun x => polynomialKernel p (v-x)) ν := by
  apply (integrable_const (μ := ν) (1 : ℝ)).mono'
    ((continuous_polynomialKernel p).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  filter_upwards with x
  change ‖polynomialKernel p (v-x)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (polynomialKernel_pos p _)]
  exact polynomialKernel_le_one p _

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] in
theorem polynomialKernel_scale_comparison (p : ℕ) (x y : V) {C : ℝ}
    (h : 1 + ‖y‖ ≤ C * (1 + ‖x‖)) :
    polynomialKernel p x ≤ C^p * polynomialKernel p y := by
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + ‖y‖) h p
  rw [mul_pow] at hh
  unfold polynomialKernel
  rw [← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (by positivity : 0 < (1 + ‖x‖)^p)
      (by positivity : 0 < (1 + ‖y‖)^p)]
  simpa only [one_mul] using hh

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] in
theorem polynomialKernel_succ_radius (p : ℕ) (z : V) {B : ℝ} (hB : B ≤ ‖z‖) :
    B * polynomialKernel (p+1) z ≤ polynomialKernel p z := by
  unfold polynomialKernel
  rw [← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (by positivity : 0 < (1 + ‖z‖)^(p+1))
      (by positivity : 0 < (1 + ‖z‖)^p), one_mul, pow_succ]
  nlinarith [pow_pos (by positivity : 0 < 1 + ‖z‖) p]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in

theorem polynomialKernel_annular_tail (ν : Measure V) [IsFiniteMeasure ν]
    (p : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hmass : ν Set.univ ≤ ENNReal.ofReal (2*B))
    (hsupp : ∀ᵐ x ∂ν, ‖x‖ ≤ 2*B) (v : V) (hv : 4*B ≤ ‖v‖) :
    (∫ x : V, polynomialKernel (p+1) (v-x) ∂ν) ≤
      2^(p+2) * polynomialKernel p v := by
  have hpoint : ∀ᵐ x ∂ν, polynomialKernel (p+1) (v-x) ≤
      2^(p+1) * polynomialKernel (p+1) v := by
    filter_upwards [hsupp] with x hx
    apply polynomialKernel_scale_comparison
    have ht := norm_add_le (v-x) x
    rw [sub_add_cancel] at ht
    linarith
  have hh := integral_mono_of_nonneg
    (ae_of_all ν (fun x => (polynomialKernel_pos (p+1) (v-x)).le))
    (integrable_const (2^(p+1) * polynomialKernel (p+1) v)) hpoint
  rw [integral_const, smul_eq_mul] at hh
  have hm : ν.real Set.univ ≤ 2*B := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*B)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  have hmul := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ (2 : ℝ)^(p+1) * polynomialKernel (p+1) v from
      mul_nonneg (by positivity) (polynomialKernel_pos (p+1) v).le)
  apply (hh.trans hmul).trans
  have hr := mul_le_mul_of_nonneg_left
    (polynomialKernel_succ_radius p v (by linarith : B ≤ ‖v‖))
    (show 0 ≤ (2 : ℝ)^(p+2) by positivity)
  convert hr using 1
  rw [show p+2 = p+1+1 by omega, pow_succ]
  ring

theorem polynomialKernel_integrable_prod (ν : Measure V) [IsFiniteMeasure ν]
    {p : ℕ} (hp : Module.finrank ℝ V < p) :
    Integrable (fun z : V × V => polynomialKernel p (z.1-z.2)) (ν.prod volume) := by
  have hc : Continuous (fun z : V × V => polynomialKernel p (z.1-z.2)) :=
    (continuous_polynomialKernel p).comp (continuous_fst.sub continuous_snd)
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  refine ⟨ae_of_all ν (fun v => (polynomialKernel_integrable hp).comp_sub_left v), ?_⟩
  have hn (z : V) : ‖polynomialKernel p z‖ = polynomialKernel p z :=
    Real.norm_of_nonneg (polynomialKernel_pos p z).le
  simpa only [hn, integral_sub_left_eq_self] using
    integrable_const (μ := ν) (∫ z : V, polynomialKernel p z)

theorem bounded_mul_polynomialKernel_integrable_prod (ν : Measure V) [IsFiniteMeasure ν]
    {p : ℕ} (hp : Module.finrank ℝ V < p) (f : V → ℝ) (hf : Continuous f)
    (hb : ∀ u : V, ‖f u‖ ≤ 1) :
    Integrable (fun z : V × V => f z.2 * polynomialKernel p (z.1-z.2))
      (ν.prod volume) := by
  apply (polynomialKernel_integrable_prod ν hp).mono
    ((hf.comp continuous_snd).mul ((continuous_polynomialKernel p).comp
      (continuous_fst.sub continuous_snd))).aestronglyMeasurable
  filter_upwards with z
  change ‖f z.2 * polynomialKernel p (z.1-z.2)‖ ≤
    ‖polynomialKernel p (z.1-z.2)‖
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb z.2)
    (norm_nonneg (polynomialKernel p (z.1-z.2)))

end KernelConvolution
end CurrentFalconer
end CriticalFourierSupport
end
end

end OAI
