import Mathlib
import OAI.Probability.Perceptron.Variational.StableLogIntensity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma finitePointMeasure_insertNth {S : Type*} [MeasurableSpace S]
    (n : ℕ) (i : Fin (n+1)) (x : S) (y : Fin n → S) :
    finitePointMeasure (n+1) (i.insertNth x y) = Measure.dirac x + finitePointMeasure n y := by
  classical
  rw [finitePointMeasure,Fin.sum_univ_succAbove _ i]
  simp [finitePointMeasure]

lemma finite_point_mecke {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ)
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y : Fin (n+1) → S, ∑ i, H (finitePointMeasure (n+1) y,y i)
      ∂Measure.pi (fun _ => ν)) = (n+1 : ℝ≥0∞) *
      ∫⁻ x, ∫⁻ y : Fin n → S, H (Measure.dirac x + finitePointMeasure n y,x)
        ∂Measure.pi (fun _ => ν) ∂ν := by
  classical
  rw [lintegral_finsetSum (f := fun (i : Fin (n+1)) (y : Fin (n+1) → S) => H (finitePointMeasure (n+1) y,y i)) _ (fun i _ => hH.comp
    ((finitePointMeasure_measurable _).prodMk (measurable_pi_apply i)))]
  have he (i : Fin (n+1)) :
      (∫⁻ y : Fin (n+1) → S, H (finitePointMeasure (n+1) y,y i)
        ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, ∫⁻ y : Fin n → S, H (Measure.dirac x + finitePointMeasure n y,x)
        ∂Measure.pi (fun _ => ν) ∂ν := by
    have hm : Measurable (fun y : Fin (n+1) → S => H (finitePointMeasure (n+1) y,y i)) :=
      hH.comp ((finitePointMeasure_measurable _).prodMk (measurable_pi_apply i))
    rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) i).symm).lintegral_comp hm]
    change (∫⁻ p : S × (Fin n → S), H (finitePointMeasure (n+1) (i.insertNth p.1 p.2),
      ((i.insertNth p.1 p.2 : Fin (n+1) → S) i)) ∂ν.prod (Measure.pi fun _ => ν)) = _
    simp only [finitePointMeasure_insertNth,Fin.insertNth_apply_same]
    exact lintegral_prod _ (hH.comp
      (((by fun_prop : Measurable (fun p : S × (Fin n → S) =>
        Measure.dirac p.1 + finitePointMeasure n p.2))).prodMk measurable_fst)).aemeasurable
  simp_rw [he]
  simp

lemma poissonMeasure_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r {n+1} * (n+1 : ℝ≥0∞) = (r : ℝ≥0∞) * poissonMeasure r {n} := by
  rw [poissonMeasure_singleton,poissonMeasure_singleton]
  have he : Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / (n+1).factorial * (n+1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp
  have hh := congrArg ENNReal.ofReal he
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-(r : ℝ)) *
    (r : ℝ)^(n+1) / (n+1).factorial), ENNReal.ofReal_mul r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one,
    ENNReal.ofReal_natCast,ENNReal.ofReal_one] using hh

lemma finitePoissonLaw_mecke {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂finitePoissonLaw r ν) =
      (r : ℝ≥0∞) * ∫⁻ x, ∫⁻ η, H (Measure.dirac x + η,x) ∂finitePoissonLaw r ν ∂ν := by
  rw [finitePoissonLaw,lintegral_sum_measure]
  simp_rw [lintegral_smul_measure]
  have hmap (n : ℕ) :
      (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂(Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)) =
      ∫⁻ y : Fin n → S, ∫⁻ x, H (finitePointMeasure n y,x) ∂finitePointMeasure n y
        ∂Measure.pi (fun _ => ν) := by
    apply lintegral_map'
    · exact aemeasurable_measure_lintegral_of_finite
        ((ae_map_iff (finitePointMeasure_measurable n).aemeasurable
          (measurableSet_lt (Measure.measurable_coe .univ) measurable_const)).mpr
            (ae_of_all _ fun y => by simp [finitePointMeasure,Measure.finsetSum_apply])) hH
    · exact (finitePointMeasure_measurable n).aemeasurable
  simp_rw [hmap]
  have hinner (n : ℕ) (y : Fin n → S) :
      (∫⁻ x, H (finitePointMeasure n y,x) ∂finitePointMeasure n y) =
        ∑ i, H (finitePointMeasure n y,y i) :=
    finitePointMeasure_lintegral (hH.comp (measurable_const.prodMk measurable_id)) _ _
  simp only [hinner,smul_eq_mul]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Fin.sum_univ_zero,lintegral_zero,mul_zero,zero_add]
  simp_rw [finite_point_mecke ν _ hH,← mul_assoc,poissonMeasure_succ_mul,mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hmn (n : ℕ) : Measurable (fun x : S => ∫⁻ y : Fin n → S,
      H (Measure.dirac x + finitePointMeasure n y,x) ∂Measure.pi (fun _ => ν)) := by
    have hm : Measurable (fun p : S × (Fin n → S) => Measure.dirac p.1 + finitePointMeasure n p.2) := by
      fun_prop
    exact (hH.comp (hm.prodMk measurable_fst)).lintegral_prod_right'
  symm
  calc
    _ = ∫⁻ x, ∑' n : ℕ, poissonMeasure r {n} * ∫⁻ y : Fin n → S,
        H (Measure.dirac x + finitePointMeasure n y,x) ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_congr
      intro x
      rw [lintegral_sum_measure]
      simp only [lintegral_smul_measure,smul_eq_mul]
      apply tsum_congr
      intro n
      congr 1
      exact lintegral_map
        (hH.comp ((measurable_const.add measurable_id).prodMk measurable_const))
        (finitePointMeasure_measurable n)
    _ = _ := by
      rw [lintegral_tsum (f := fun (n : ℕ) (x : S) => poissonMeasure r {n} *
        ∫⁻ y : Fin n → S, H (Measure.dirac x + finitePointMeasure n y,x) ∂Measure.pi (fun _ => ν))
        (fun n => (measurable_const.mul (hmn n)).aemeasurable)]
      apply tsum_congr
      intro n
      exact lintegral_const_mul' _ _ (measure_ne_top _ _)

def stableLaplaceConstant (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1-Real.exp (-Real.exp x)) ∂stableLogIntensity b

lemma one_sub_exp_neg_le_min {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 1-Real.exp (-u) ∧ 1-Real.exp (-u) ≤ min u 1 := by
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu))
  · exact le_min (by linarith [Real.add_one_le_exp (-u)]) (by linarith [Real.exp_pos (-u)])

lemma stableLaplaceConstant_finite {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b ≠ ⊤ := by
  apply ne_top_of_le_ne_top (stableLogIntensity_min_exp_finite hb0 hb1)
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (one_sub_exp_neg_le_min (Real.exp_pos x).le).2

lemma stableLaplaceConstant_positive {b : ℝ} (hb : 0 < b) :
    0 < stableLaplaceConstant b := by
  unfold stableLaplaceConstant
  rw [lintegral_pos_iff_support (by fun_prop)]
  have he : Function.support (fun x : ℝ => ENNReal.ofReal (1-Real.exp (-Real.exp x))) = univ := by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by
      have hh := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos x))
      linarith))
  rw [he,stableLogIntensity_univ hb]
  simp

lemma stableLaplaceExponent_scaling {b t : ℝ} (hb : 0 ≤ b) (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (1-Real.exp (-(t*Real.exp x))) ∂stableLogIntensity b) =
      ENNReal.ofReal (t^b) * stableLaplaceConstant b := by
  have he := stableLogIntensity_lintegral_translate hb (Real.log t)
    (f := fun x => ENNReal.ofReal (1-Real.exp (-Real.exp x))) (by fun_prop)
  have hx (x : ℝ) : Real.exp (x+Real.log t) = t*Real.exp x := by
    rw [Real.exp_add,Real.exp_log ht]
    exact mul_comm _ _
  simp_rw [hx] at he
  convert he using 1
  rw [Real.rpow_def_of_pos ht,mul_comm b (Real.log t)]
  rfl

def stablePoissonTotal (η : Measure ℝ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η).toReal

lemma stablePoissonTotal_measurable : Measurable stablePoissonTotal :=
  ENNReal.measurable_toReal.comp (Measure.measurable_lintegral (by fun_prop))

lemma stablePoissonTotal_pos {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b), 0 < stablePoissonTotal η := by
  filter_upwards [stablePoisson_total_positive hb0,stablePoisson_total_finite hb0 hb1] with η hp hf
  exact ENNReal.toReal_pos hp.ne' hf

lemma stablePoissonTotal_laplace {b t : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (∫ η, Real.exp (-t*stablePoissonTotal η) ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      Real.exp (-(stableLaplaceConstant b).toReal * t^b) := by
  have he := poissonRandomMeasureLaw_laplace (stableLogIntensity b)
    (f := fun x => t*Real.exp x) (by fun_prop) (fun x => mul_nonneg ht.le (Real.exp_pos x).le)
  rw [stableLaplaceExponent_scaling hb0.le ht,
    expNegENNReal_finite (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (stableLaplaceConstant_finite hb0 hb1)),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ht b).le] at he
  convert he using 1
  · apply integral_congr_ae
    filter_upwards [stablePoisson_total_finite hb0 hb1] with η hη
    simp only [poissonLaplace,ENNReal.ofReal_mul ht.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      expNegENNReal_finite (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hη),
      ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le]
    congr 1
    dsimp [stablePoissonTotal]
    ring
  · congr 1
    ring

lemma standardGaussian_integrationByParts {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hm : Measurable F')
    {C D : ℝ} (hb : ∀ x, |F x| ≤ C) (hb' : ∀ x, |F' x| ≤ D) :
    ∫ x, x * F x ∂gaussianReal 0 1 = ∫ x, F' x ∂gaussianReal 0 1 := by
  have hfm : Measurable F := (continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)).measurable
  have h1 : Integrable (fun x => gaussianPDFReal 0 1 x * F' x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb' x)
  have h2 : Integrable (fun x => (-x * gaussianPDFReal 0 1 x) * F x) := by
    have hh := standardGaussian_density_mul_integrable.neg.mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
    simpa only [neg_mul,Pi.neg_apply] using hh
  have h3 : Integrable (fun x => gaussianPDFReal 0 1 x * F x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => standardGaussian_density_deriv x) (fun x _ => hF x) h1 h2 h3
  simp only [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul]
  rw [he]
  simp only [neg_mul,integral_neg,neg_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

section Tilt
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

def tiltIntegral (v F : S → ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (t * v x) * F x ∂μ

def tiltPartition (v : S → ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (t * v x) ∂μ

def tiltMean (v F : S → ℝ) (t : ℝ) : ℝ := tiltIntegral μ v F t / tiltPartition μ v t

lemma tilt_integrable {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    Integrable (fun x => Real.exp (t * v x) * F x) μ := by
  refine Integrable.of_bound (hv.const_mul t |>.exp.mul hF).aestronglyMeasurable
    (Real.exp (|t| * C) * D) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (hFD x) (abs_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * v x)).trans (by rw [abs_mul]; gcongr; exact hvC x)

lemma tilt_integral_deriv {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    HasDerivAt (tiltIntegral μ v F)
      (∫ x, Real.exp (t * v x) * v x * F x ∂μ) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t 1) (bound := fun _ => Real.exp ((|t|+1)*C) * C * D)
    (F' := fun u x => Real.exp (u * v x) * v x * F x) (Metric.ball_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun u => (hv.const_mul u |>.exp.mul hF).aestronglyMeasurable)
    (tilt_integrable μ hv hF hC hD hvC hFD t)
    (by fun_prop) (ae_of_all _ fun x u hu => ?_) (integrable_const _)
    (ae_of_all _ fun x u _ => ?_)).2
  · have hu' : |u| ≤ |t|+1 := by
      have hh : |u-t| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hu
      calc
        |u| = |(u-t)+t| := by congr 1; ring
        _ ≤ |u-t|+|t| := abs_add_le _ _
        _ ≤ |t|+1 := by linarith
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (u * v x) ≤ Real.exp ((|t|+1)*C) := by
      apply Real.exp_le_exp.mpr
      apply (le_abs_self (u * v x)).trans
      rw [abs_mul]
      exact mul_le_mul hu' (hvC x) (abs_nonneg _) (by positivity)
    exact mul_le_mul (mul_le_mul hexp (hvC x) (abs_nonneg _) (Real.exp_pos _).le)
      (hFD x) (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hC)
  · convert! (((hasDerivAt_id u).mul_const (v x)).exp.mul_const (F x)) using 1
    simp only [one_mul,id_eq]

lemma tilt_partition_pos {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    0 < tiltPartition μ v t := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC (by norm_num : (0:ℝ) ≤ 1)
      hvC (fun _ => by norm_num) t
  have he : Real.exp (- |t| * C) ≤ tiltPartition μ v t := by
    calc
      Real.exp (- |t| * C) = ∫ _ : S, Real.exp (- |t| * C) ∂μ := by simp
      _ ≤ tiltPartition μ v t := integral_mono_ae (integrable_const _) hi (ae_of_all _ fun x => by
        apply Real.exp_le_exp.mpr
        have hh : |t*v x| ≤ |t| * C := by rw [abs_mul]; gcongr; exact hvC x
        nlinarith [neg_abs_le (t*v x)])
  exact (Real.exp_pos _).trans_le he

lemma tilt_partition_deriv {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    HasDerivAt (tiltPartition μ v) (tiltIntegral μ v v t) t := by
  have hd := tilt_integral_deriv μ (F := fun _ => 1) hv measurable_const hC
    (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  change HasDerivAt (fun u => ∫ x, Real.exp (u * v x) * 1 ∂μ)
    (∫ x, Real.exp (t*v x) * v x * 1 ∂μ) t at hd
  change HasDerivAt (fun u => ∫ x, Real.exp (u * v x) ∂μ)
    (∫ x, Real.exp (t * v x) * v x ∂μ) t
  simpa only [mul_one] using hd

lemma tilt_mean_deriv {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    HasDerivAt (tiltMean μ v F)
      (tiltMean μ v (fun x => v x * F x) t - tiltMean μ v F t * tiltMean μ v v t) t := by
  have hp := (tilt_partition_pos μ hv hC hvC t).ne'
  have hd := (tilt_integral_deriv μ hv hF hC hD hvC hFD t).div
    (tilt_partition_deriv μ hv hC hvC t) hp
  convert! hd using 1
  simp only [tiltMean,tiltIntegral,mul_assoc]
  field_simp

lemma tilt_mean_bound {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    |tiltMean μ v F t| ≤ D := by
  have hp := tilt_partition_pos μ hv hC hvC t
  have hi := tilt_integrable μ hv hF hC hD hvC hFD t
  have hiExp : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  rw [tiltMean,abs_div,abs_of_pos hp,div_le_iff₀ hp]
  calc
    |tiltIntegral μ v F t| ≤ ∫ x, |Real.exp (t * v x) * F x| ∂μ := by
      simpa only [tiltIntegral,Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => Real.exp (t * v x) * F x)
    _ ≤ ∫ x, Real.exp (t * v x) * D ∂μ := by
      apply integral_mono_ae hi.norm (hiExp.mul_const D)
      exact ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs]
        rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hFD x) (Real.exp_pos _).le
    _ = D * tiltPartition μ v t := by rw [integral_mul_const]; exact mul_comm _ _

def tiltLaw (v : S → ℝ) (t : ℝ) : Measure S :=
  (ENNReal.ofReal (tiltPartition μ v t))⁻¹ •
    μ.withDensity (fun x => ENNReal.ofReal (Real.exp (t * v x)))

lemma tilt_law_probability {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    IsProbabilityMeasure (tiltLaw μ v t) := by
  have hp := tilt_partition_pos μ hv hC hvC t
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  constructor
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ .univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le)]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top

lemma tilt_law_integral {v F : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    ∫ x, F x ∂tiltLaw μ v t = tiltMean μ v F t := by
  rw [tiltLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (Real.exp (t * v x))) from (hv.const_mul t).exp.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (tilt_partition_pos μ hv hC hvC t).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,tiltMean,tiltIntegral]
  exact (div_eq_inv_mul _ _).symm

lemma tilt_mean_continuous {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) :
    Continuous (tiltMean μ v F) :=
  continuous_iff_continuousAt.mpr fun t => (tilt_mean_deriv μ hv hF hC hD hvC hFD t).continuousAt

lemma gaussian_tilt_integrationByParts {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) :
    (∫ t, t * tiltMean μ v F t ∂gaussianReal 0 1) =
      ∫ t, tiltMean μ v (fun x => v x * F x) t -
        tiltMean μ v F t * tiltMean μ v v t ∂gaussianReal 0 1 := by
  have hvF : ∀ x, |v x * F x| ≤ C * D := fun x => by
    rw [abs_mul]; exact mul_le_mul (hvC x) (hFD x) (abs_nonneg _) hC
  apply standardGaussian_integrationByParts
    (fun t => tilt_mean_deriv μ hv hF hC hD hvC hFD t)
    ((tilt_mean_continuous μ hv (hv.mul hF) hC (mul_nonneg hC hD) hvC hvF).measurable.sub
      ((tilt_mean_continuous μ hv hF hC hD hvC hFD).measurable.mul
        (tilt_mean_continuous μ hv hv hC hC hvC hvC).measurable))
    (fun t => tilt_mean_bound μ hv hF hC hD hvC hFD t)
    (D := 2*C*D)
  intro t
  calc
    |tiltMean μ v (fun x => v x * F x) t - tiltMean μ v F t * tiltMean μ v v t| ≤
        |tiltMean μ v (fun x => v x * F x) t| + |tiltMean μ v F t * tiltMean μ v v t| := abs_sub _ _
    _ ≤ C*D + D*C := add_le_add (tilt_mean_bound μ hv (hv.mul hF) hC (mul_nonneg hC hD) hvC hvF t)
      (by
        rw [abs_mul]
        exact mul_le_mul (tilt_mean_bound μ hv hF hC hD hvC hFD t)
          (tilt_mean_bound μ hv hv hC hC hvC hvC t) (abs_nonneg _) hD)
    _ = 2*C*D := by ring

end Tilt

def replicaPotential {S : Type*} (v : S → ℝ) (n : ℕ) (x : Fin n → S) : ℝ := ∑ i, v (x i)

lemma replicaPotential_measurable {S : Type*} [MeasurableSpace S]
    {v : S → ℝ} (hv : Measurable v) (n : ℕ) : Measurable (replicaPotential v n) := by
  exact Finset.measurable_sum _ fun i _ => hv.comp (measurable_pi_apply i)

lemma replicaPotential_bound {S : Type*} {v : S → ℝ} {C : ℝ}
    (hv : ∀ x, |v x| ≤ C) (n : ℕ) (x : Fin n → S) :
    |replicaPotential v n x| ≤ n*C := by
  calc
    |∑ i, v (x i)| ≤ ∑ i, |v (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, C := Finset.sum_le_sum (fun i _ => hv (x i))
    _ = n*C := by simp

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replica_partition {v : S → ℝ} (_hv : Measurable v) (n : ℕ) (t : ℝ) :
    tiltPartition (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      (tiltPartition μ v t)^n := by
  unfold tiltPartition replicaPotential
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x))]
  simp

lemma replica_mean_potential {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) (replicaPotential v n) t =
      n * tiltMean μ v v t := by
  have hd := tilt_partition_deriv (Measure.pi fun _ : Fin n => μ)
    (replicaPotential_measurable hv n) (mul_nonneg (Nat.cast_nonneg n) hC)
    (replicaPotential_bound hvC n) t
  have he : tiltPartition (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) =
      fun u => (tiltPartition μ v u)^n := funext (replica_partition μ hv n)
  rw [he] at hd
  have hg := (tilt_partition_deriv μ hv hC hvC t).pow n
  have hder := hd.unique hg
  unfold tiltMean
  rw [hder,replica_partition μ hv n]
  have hp := (tilt_partition_pos μ hv hC hvC t).ne'
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp

end SphericalPerceptronFreeEnergy
end

end OAI
