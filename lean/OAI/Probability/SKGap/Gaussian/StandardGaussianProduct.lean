import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap

theorem hasDerivAt_gaussianPDFReal (d : ℝ) {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    HasDerivAt (gaussianPDFReal d s)
      (-(y - d) / (s : ℝ) * gaussianPDFReal d s y) y := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  unfold gaussianPDFReal
  convert! (((((hasDerivAt_id y).sub_const d).pow 2).neg.div_const
    (2 * (s : ℝ))).exp).const_mul (1 / sqrt (2 * π * (s : ℝ))) using 1
  · ext x
    simp only [one_div, Pi.neg_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    norm_num
    ring

theorem integrable_gaussian_iff {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal d s) ↔ Integrable (fun y => gaussianPDFReal d s y * f y) := by
  rw [gaussianReal_of_var_ne_zero d hs,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF d s)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]

theorem gaussian_integration_by_parts {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    {f f' : ℝ → ℝ} (hd : ∀ y, HasDerivAt f (f' y) y)
    (hf : Integrable f (gaussianReal d s)) (hf' : Integrable f' (gaussianReal d s))
    (hyf : Integrable (fun y => (y - d) * f y) (gaussianReal d s)) :
    (∫ y, (y - d) * f y ∂gaussianReal d s) =
      (s : ℝ) * (∫ y, f' y ∂gaussianReal d s) := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hfg := (integrable_gaussian_iff hs).mp hf
  have hf'g := (integrable_gaussian_iff hs).mp hf'
  have hyfg := (integrable_gaussian_iff hs).mp hyf
  have hder (y : ℝ) : HasDerivAt (fun y => gaussianPDFReal d s y * f y)
      (gaussianPDFReal d s y * f' y -
        (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) y := by
    convert! (hasDerivAt_gaussianPDFReal d hs y).mul (hd y) using 1
    ring
  have hii : Integrable (fun y => gaussianPDFReal d s y * f' y -
      (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) :=
    hf'g.sub (hyfg.div_const _)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hder hii hfg
  rw [integral_sub hf'g (hyfg.div_const (s : ℝ)), integral_div] at hz
  rw [integral_gaussianReal_eq_integral_smul hs,
    integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  have he : (∫ y, gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ) =
      ∫ y, gaussianPDFReal d s y * f' y := by linarith
  have hm := (div_eq_iff hsp.ne').mp he
  nlinarith only [hm]

def standardGaussianProduct (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (n : ℕ) : IsProbabilityMeasure (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  infer_instance

theorem continuous_insertNth {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℝ) :
    Continuous (fun z : ℝ => i.insertNth (α := fun _ => ℝ) z u) := by
  apply continuous_pi
  refine i.forall_iff_succAbove.mpr ⟨?_, ?_⟩
  · simp only [Fin.insertNth_apply_same]
    convert! (continuous_id : Continuous (fun x : ℝ => x)) using 1
  · intro k
    simpa only [Fin.insertNth_apply_succAbove] using
      (continuous_const : Continuous (fun _ : ℝ => u k))

theorem gaussianProduct_coordinate_IBP {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ} {C D : ℝ}
    (hf : Continuous f) (hdf : Continuous df)
    (hfbound : ∀ x, ‖f x‖ ≤ C) (hdfbound : ∀ x, ‖df x‖ ≤ D)
    (hder : ∀ (u : Fin n → ℝ) (z : ℝ),
      HasDerivAt (fun z => f (i.insertNth z u)) (df (i.insertNth z u)) z) :
    (∫ x, x i * f x ∂standardGaussianProduct (n + 1)) =
      ∫ x, df x ∂standardGaussianProduct (n + 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hp : MeasurePreserving e.symm
      ((gaussianReal 0 1).prod (standardGaussianProduct n))
      (standardGaussianProduct (n + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) i).symm
  have hi : Integrable (fun x : Fin (n + 1) → ℝ => x i * f x)
      (standardGaussianProduct (n + 1)) := by
    simpa only [mul_comm, standardGaussianProduct] using
      (integrable_eval (i := i) IsGaussian.integrable_id).bdd_mul
        hf.aestronglyMeasurable (ae_of_all _ hfbound)
  have hi' : Integrable df (standardGaussianProduct (n + 1)) :=
    Integrable.of_bound hdf.aestronglyMeasurable D (ae_of_all _ hdfbound)
  have hsplit (g : (Fin (n + 1) → ℝ) → ℝ)
      (hg : Integrable g (standardGaussianProduct (n + 1))) :
      (∫ x, g x ∂standardGaussianProduct (n + 1)) =
        ∫ u, ∫ z, g (i.insertNth z u) ∂gaussianReal 0 1 ∂standardGaussianProduct n := by
    have hi2 : Integrable (fun x => g (e.symm x))
        ((gaussianReal 0 1).prod (standardGaussianProduct n)) :=
      hp.integrable_comp_of_integrable hg
    rw [← hp.integral_comp' g, integral_prod _ hi2]
    rw [integral_integral_swap hi2]
    rfl
  rw [hsplit _ hi, hsplit _ hi']
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Fin.insertNth_apply_same]
  have hfu : Integrable (fun z => f (i.insertNth z u)) (gaussianReal 0 1) :=
    Integrable.of_bound (hf.comp (continuous_insertNth i u)).aestronglyMeasurable C
      (ae_of_all _ (fun z => hfbound _))
  have hdfu : Integrable (fun z => df (i.insertNth z u)) (gaussianReal 0 1) :=
    Integrable.of_bound (hdf.comp (continuous_insertNth i u)).aestronglyMeasurable D
      (ae_of_all _ (fun z => hdfbound _))
  have hzfu : Integrable (fun z => z * f (i.insertNth z u)) (gaussianReal 0 1) := by
    simpa only [mul_comm, id_eq, Function.comp_def] using (IsGaussian.integrable_id (μ := gaussianReal 0 1)).bdd_mul
      (hf.comp (continuous_insertNth i u)).aestronglyMeasurable
      (ae_of_all _ (fun z => hfbound _))
  simpa only [NNReal.coe_one, sub_zero, one_mul] using
    gaussian_integration_by_parts (d := 0) (s := 1) one_ne_zero (hder u) hfu hdfu
      (by simpa only [sub_zero] using hzfu)

end SKGap

open Filter
open scoped Topology
namespace SKGap
lemma tendsto_gaussianPDFReal_atTop (d : ℝ) {s : ℝ≥0} (hs : 0 < s) :
    Filter.Tendsto (gaussianPDFReal d s) Filter.atTop (𝓝 0) := by
  have hsp : (0:ℝ) < s := hs
  have hshift : Tendsto (fun x : ℝ => x-d) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b+d)] with x hx
    linarith
  have hpow : Filter.Tendsto (fun x : ℝ => (x-d)^2) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp hshift
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.atTop_div_const (by positivity : 0 < 2*(s:ℝ)))
  rw [gaussianPDFReal_def]
  simpa only [neg_div, mul_zero,one_div,Function.comp_apply] using hexp.const_mul (1/sqrt (2*Real.pi*(s:ℝ)))

lemma tendsto_gaussianPDFReal_neg_atTop (d : ℝ) {s : ℝ≥0} (hs : 0 < s) :
    Filter.Tendsto (fun x => gaussianPDFReal d s (-x)) Filter.atTop (𝓝 0) := by
  have he : (fun x => gaussianPDFReal d s (-x)) = gaussianPDFReal (-d) s := by
    funext x
    unfold gaussianPDFReal
    congr 2
    ring
  rw [he]
  exact tendsto_gaussianPDFReal_atTop (-d) hs

theorem gaussian_lipschitz_IBP {f : ℝ → ℝ} {L : ℝ≥0} {C d : ℝ} {s : ℝ≥0}
    (hs : 0 < s) (hL : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ y, (y-d)*f y ∂gaussianReal d s) = (s:ℝ)*(∫ y, deriv f y ∂gaussianReal d s) := by
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hdf : Integrable (deriv f) (gaussianReal d s) :=
    Integrable.of_bound (measurable_deriv f).aestronglyMeasurable (L:ℝ)
      (ae_of_all _ (fun _ => norm_deriv_le_of_lipschitz hL))
  have hyf : Integrable (fun y => (y-d)*f y) (gaussianReal d s) := by
    have hh := ((IsGaussian.integrable_id (μ := gaussianReal d s)).sub (integrable_const d)).bdd_mul
      (f := f) hL.continuous.aestronglyMeasurable (ae_of_all _ hC)
    simpa only [mul_comm,Pi.sub_apply,id_eq] using hh
  let p := gaussianPDFReal d s
  have hpi : Integrable (fun y => p y*deriv f y) := (integrable_gaussian_iff hs.ne').mp hdf
  have hxi : Integrable (fun y => p y*((y-d)*f y)) := (integrable_gaussian_iff hs.ne').mp hyf
  let g : ℝ → ℝ := fun y => p y*deriv f y-(p y*((y-d)*f y))/(s:ℝ)
  have hgi : Integrable g := hpi.sub (hxi.div_const _)
  have hpd (y : ℝ) : deriv p y = -(y-d)/(s:ℝ)*p y := (hasDerivAt_gaussianPDFReal d hs.ne' y).deriv
  have hpac (a b : ℝ) : AbsolutelyContinuousOnInterval p a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    have hh : ContDiff ℝ 1 p := by
      change ContDiff ℝ 1 (fun x : ℝ => (sqrt (2 * π * (s : ℝ)))⁻¹ * exp (-(x-d)^2/(2*(s:ℝ))))
      fun_prop
    exact hh.contDiffOn
  have hfac (a b : ℝ) : AbsolutelyContinuousOnInterval f a b := hL.lipschitzOnWith.absolutelyContinuousOnInterval
  have hftc (a b : ℝ) : (∫ y in a..b, g y) = p b*f b-p a*f a := by
    rw [← (hpac a b).integral_deriv_mul_eq_sub (hfac a b)]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [g]
    rw [hpd]
    ring
  have hbd (u : ℝ → ℝ) (hp : Filter.Tendsto (fun x => p (u x)) Filter.atTop (𝓝 0)) :
      Filter.Tendsto (fun x => p (u x)*f (u x)) Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun x => ?_) (by simpa only [zero_mul] using hp.mul_const C)
    rw [norm_mul, Real.norm_eq_abs (p (u x)),abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_left (hC _) (gaussianPDFReal_nonneg _ _ _)
  have htop := hbd id (tendsto_gaussianPDFReal_atTop d hs)
  have hbot := hbd Neg.neg (tendsto_gaussianPDFReal_neg_atTop d hs)
  have hlim := intervalIntegral_tendsto_integral hgi Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  simp only [hftc] at hlim
  have hz : (∫ y, g y) = 0 := by
    simpa only [id_eq,sub_zero] using tendsto_nhds_unique hlim (htop.sub hbot)
  dsimp [g] at hz
  rw [integral_sub hpi (hxi.div_const _),integral_div] at hz
  rw [integral_gaussianReal_eq_integral_smul hs.ne',integral_gaussianReal_eq_integral_smul hs.ne']
  simp only [smul_eq_mul]
  have hh : (∫ y, p y*((y-d)*f y))/(s:ℝ) = ∫ y, p y*deriv f y := by linarith
  have hm := (div_eq_iff (ne_of_gt (show (0:ℝ) < s from hs))).mp hh
  dsimp [p] at hm
  nlinarith only [hm]

end SKGap

end

end OAI
