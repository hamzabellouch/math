import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatMoments
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! Holomorphic dependence of the Fourier heat integral on a complex
height with positive real part. All majorants are actual heat integrals. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def cubicThetaComplexHeightHeat (s : ℂ) (A : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (t:ℂ)^(s-2)*Complex.exp (-z*((t+A/t:ℝ):ℂ))

def cubicThetaHeightMajorant (s : ℂ) (A d t : ℝ) : ℝ :=
  t^(s.re-2)*Real.exp (-d*(t+A/t))

lemma cubicThetaComplexHeightHeat_norm (s z : ℂ) (A : ℝ) {t : ℝ} (ht : 0<t) :
    ‖cubicThetaComplexHeightHeat s A z t‖=cubicThetaHeightMajorant s A z.re t := by
  rw [cubicThetaComplexHeightHeat,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_exp]
  simp [cubicThetaHeightMajorant,Complex.mul_re]

lemma cubicThetaHeightMajorant_eq (s : ℂ) (A : ℝ) {d : ℝ} (hd : 0<d)
    {t : ℝ} (ht : 0<t) :
    cubicThetaHeightMajorant s A d t=‖cubicThetaDualHeat (Real.sqrt d) s (A*d) t‖ := by
  rw [cubicThetaDualHeat_norm _ _ _ ht,Real.sq_sqrt hd.le]
  unfold cubicThetaHeightMajorant
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

lemma cubicThetaHeightMajorant_integrable (s : ℂ) {A d : ℝ} (hA : 0<A) (hd : 0<d) :
    IntegrableOn (cubicThetaHeightMajorant s A d) (Ioi 0) := by
  apply (cubicThetaNonzeroHeat_integrable (Real.sqrt_pos.mpr hd) (mul_pos hA hd) s).norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (cubicThetaHeightMajorant_eq s A hd ht).symm

lemma cubicThetaHeightDerivative_integrable (s : ℂ) {A d : ℝ} (hA : 0<A) (hd : 0<d) :
    IntegrableOn (fun t => (t+A/t)*cubicThetaHeightMajorant s A d t) (Ioi 0) := by
  have hp := cubicThetaHeightMajorant_integrable (s+1) hA hd
  have hm := (cubicThetaHeightMajorant_integrable (s-1) hA hd).const_mul A
  apply (hp.add hm).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : t*t^(s.re-2)=t^((s+1).re-2) := by
    calc
      _ = t^(1:ℝ)*t^(s.re-2) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add ht]
        congr 1
        simp only [Complex.add_re,Complex.one_re]
        ring
  have ht2 : t^(s.re-2)/t=t^((s-1).re-2) := by
    calc
      _ = t^(s.re-2)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_sub ht]
        congr 1
        simp only [Complex.sub_re,Complex.one_re]
        ring
  simp only [Pi.add_apply,cubicThetaHeightMajorant]
  rw [← ht1,← ht2]
  ring

lemma cubicThetaComplexHeightHeat_bound (s : ℂ) {A d : ℝ} (hA : 0<A) (_hd : 0<d)
    {z : ℂ} (hz : d≤z.re) {t : ℝ} (ht : 0<t) :
    ‖cubicThetaComplexHeightHeat s A z t‖≤cubicThetaHeightMajorant s A d t := by
  rw [cubicThetaComplexHeightHeat_norm s z A ht]
  unfold cubicThetaHeightMajorant
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg ht.le _)
  have hm : 0≤t+A/t := by positivity
  simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hz hm)

lemma cubicThetaComplexHeightHeat_deriv (s z : ℂ) (A t : ℝ) :
    HasDerivAt (fun w => cubicThetaComplexHeightHeat s A w t)
      (-((t+A/t:ℝ):ℂ)*cubicThetaComplexHeightHeat s A z t) z := by
  have h := (((hasDerivAt_id z).neg.mul_const ((t+A/t:ℝ):ℂ)).cexp).const_mul
    ((t:ℂ)^(s-2))
  convert h using 1
  · rfl
  · dsimp only [cubicThetaComplexHeightHeat,Pi.neg_apply,id_eq]
    ring

def cubicThetaComplexHeightIntegral (s : ℂ) (A : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0:ℝ), cubicThetaComplexHeightHeat s A z t

lemma cubicThetaComplexHeightIntegral_differentiableAt (s : ℂ) {A : ℝ} (hA : 0<A)
    {z : ℂ} (hz : 0<z.re) :
    DifferentiableAt ℂ (cubicThetaComplexHeightIntegral s A) z := by
  let d := z.re/2
  have hd : 0<d := half_pos hz
  let U : Set ℂ := {w | d<w.re}
  have hU : U∈𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show d<z.re by dsimp [d]; linarith)
  let F' (w : ℂ) (t : ℝ) := -((t+A/t:ℝ):ℂ)*cubicThetaComplexHeightHeat s A w t
  have hmeas (w : ℂ) : AEStronglyMeasurable (cubicThetaComplexHeightHeat s A w)
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaComplexHeightHeat
    fun_prop
  have hint : IntegrableOn (cubicThetaComplexHeightHeat s A z) (Ioi 0) := by
    apply (cubicThetaHeightMajorant_integrable s hA hd).mono' (hmeas z)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicThetaComplexHeightHeat_bound s hA hd (by dsimp [d]; linarith) ht
  have hderivmeas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    dsimp [F',cubicThetaComplexHeightHeat]
    fun_prop
  have hb : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), ∀ w∈U,
      ‖F' w t‖≤(t+A/t)*cubicThetaHeightMajorant s A d t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0<t at ht
    intro w hw
    change d<w.re at hw
    dsimp only [F']
    rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<t+A/t)]
    exact mul_le_mul_of_nonneg_left (cubicThetaComplexHeightHeat_bound s hA hd hw.le ht)
      (by positivity)
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), ∀ w∈U,
      HasDerivAt (fun w => cubicThetaComplexHeightHeat s A w t) (F' w t) w :=
    Filter.Eventually.of_forall (fun t w _ => cubicThetaComplexHeightHeat_deriv s w A t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    (Filter.Eventually.of_forall hmeas) hint hderivmeas hb
    (cubicThetaHeightDerivative_integrable s hA hd) hdiff).2.differentiableAt

theorem cubicThetaComplexHeightIntegral_analytic (s : ℂ) {A : ℝ} (hA : 0<A)
    {z : ℂ} (hz : 0<z.re) : AnalyticAt ℂ (cubicThetaComplexHeightIntegral s A) z := by
  have hd : DifferentiableOn ℂ (cubicThetaComplexHeightIntegral s A) {w : ℂ | 0<w.re} :=
    fun w hw => (cubicThetaComplexHeightIntegral_differentiableAt s hA hw).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

end CubicFirstMoment

end

end OAI
