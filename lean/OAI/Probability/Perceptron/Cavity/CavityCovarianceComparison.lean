import Mathlib
import OAI.Probability.Perceptron.Variational.IntegratedConvex

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma bounded_log_partition_path_derivative {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (H D : ℝ→S→ℝ)
    (hH : ∀ t,Measurable (H t)) (hD : ∀ t,Measurable (D t))
    {A B : ℝ} (hA : ∀ t s,|H t s|≤A) (hB : ∀ t s,|D t s|≤B)
    (hd : ∀ t s,HasDerivAt (fun u=>H u s) (D t s) t) (t : ℝ) :
    HasDerivAt (fun u=>Real.log (tiltPartition μ (H u) 1))
      (tiltMean μ (H t) (D t) 1) t := by
  have hi (u : ℝ) : Integrable (fun s=>Real.exp (H u s)) μ :=
    Integrable.of_bound (hH u).exp.aestronglyMeasurable (Real.exp A)
      (ae_of_all _ fun s=>by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (le_abs_self _ |>.trans (hA u s)))
  have hp (u : ℝ) : 0<∫ s,Real.exp (H u s) ∂μ := by
    apply integral_pos_iff_support_of_nonneg (fun s=>(Real.exp_pos _).le) (hi u) |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun u s=>Real.exp (H u s)) (F':=fun u s=>Real.exp (H u s)*D u s)
    (s:=univ) (bound:=fun _ : S=>Real.exp A*B) (x₀:=t)
    (by simp : univ∈𝓝 t) (Eventually.of_forall fun u=>(hH u).exp.aestronglyMeasurable)
    (hi t) (((hH t).exp.mul (hD t)).aestronglyMeasurable)
    (ae_of_all _ fun s u _=>by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (le_abs_self _ |>.trans (hA u s)))
        (hB u s) (abs_nonneg _) (Real.exp_pos _).le)
    (integrable_const _) (ae_of_all _ fun s u _=>(hd u s).exp)
  simpa only [tiltMean,tiltIntegral,tiltPartition,one_mul] using hh.2.log (hp t).ne'

variable {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]

def cavityGaussianRotation (V W : S→EuclideanSpace ℝ I) (t : ℝ) (s : S) : EuclideanSpace ℝ I :=
  Real.cos t •V s+Real.sin t •W s

def cavityGaussianRotationVelocity (V W : S→EuclideanSpace ℝ I) (t : ℝ) (s : S) : EuclideanSpace ℝ I :=
  (-Real.sin t) •V s+Real.cos t •W s

lemma cavityGaussianRotation_norm {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    {V W : S→EuclideanSpace ℝ I} {C : ℝ} (_hC : 0≤C)
    (hV : ∀ s,‖V s‖≤C) (hW : ∀ s,‖W s‖≤C) (t : ℝ) (s : S) :
    ‖cavityGaussianRotation V W t s‖≤2*C := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  have h1 := mul_le_mul (Real.abs_cos_le_one t) (hV s) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h2 := mul_le_mul (Real.abs_sin_le_one t) (hW s) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  linarith

lemma cavityGaussianRotationVelocity_norm {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    {V W : S→EuclideanSpace ℝ I} {C : ℝ} (_hC : 0≤C)
    (hV : ∀ s,‖V s‖≤C) (hW : ∀ s,‖W s‖≤C) (t : ℝ) (s : S) :
    ‖cavityGaussianRotationVelocity V W t s‖≤2*C := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,abs_neg]
  have h1 := mul_le_mul (Real.abs_sin_le_one t) (hV s) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h2 := mul_le_mul (Real.abs_cos_le_one t) (hW s) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  linarith

variable (μ : Measure S) [IsProbabilityMeasure μ] {H : S→ℝ} {V W : S→EuclideanSpace ℝ I}
  (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
  {A C : ℝ} (hA : 0≤A) (hC : 0≤C) (hHA : ∀ s,|H s|≤A)
  (hVC : ∀ s,‖V s‖≤C) (hWC : ∀ s,‖W s‖≤C)

include hH hV hW hA hC hHA hVC hWC

omit hH hV hW hA hC hHA hVC hWC in
lemma cavityGaussianRotation_log_derivative
    {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H : S→ℝ} {V W : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
    {A C : ℝ} (_hA : 0≤A) (hC : 0≤C) (hHA : ∀ s,|H s|≤A)
    (hVC : ∀ s,‖V s‖≤C) (hWC : ∀ s,‖W s‖≤C)
    (g : EuclideanSpace ℝ I) (t : ℝ) :
    HasDerivAt (fun u=>Real.log (tiltPartition μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1))
      (tiltMean μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g)
        (fun s=>inner ℝ (cavityGaussianRotationVelocity V W t s) g) 1) t := by
  have hv (u : ℝ) : Measurable (cavityGaussianRotation V W u) := by unfold cavityGaussianRotation; fun_prop
  have hw (u : ℝ) : Measurable (cavityGaussianRotationVelocity V W u) := by unfold cavityGaussianRotationVelocity; fun_prop
  apply bounded_log_partition_path_derivative μ _ _
    (fun u=>hH.add ((hv u).inner measurable_const))
    (fun u=>(hw u).inner measurable_const)
    (A:=A+2*C*‖g‖) (B:=2*C*‖g‖)
  · intro u s
    exact (abs_add_le _ _).trans (add_le_add (hHA s)
      ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        (cavityGaussianRotation_norm hC hVC hWC u s) (norm_nonneg g))))
  · intro u s
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (cavityGaussianRotationVelocity_norm hC hVC hWC u s) (norm_nonneg g))
  · intro u s
    simpa [cavityGaussianRotation,cavityGaussianRotationVelocity,inner_add_left,inner_smul_left] using
      ((((Real.hasDerivAt_cos u).mul_const (inner ℝ (V s) g)).add
        ((Real.hasDerivAt_sin u).mul_const (inner ℝ (W s) g))).const_add (H s))

lemma cavityGaussianRotation_mean_derivative (t : ℝ) :
    HasDerivAt (fun u=>∫ g,Real.log (tiltPartition μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1) ∂stdGaussian (EuclideanSpace ℝ I))
      (∫ g,tiltMean μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g)
        (fun s=>inner ℝ (cavityGaussianRotationVelocity V W t s) g) 1
        ∂stdGaussian (EuclideanSpace ℝ I)) t := by
  have hv (u : ℝ) : Measurable (cavityGaussianRotation V W u) := by unfold cavityGaussianRotation; fun_prop
  have hw (u : ℝ) : Measurable (cavityGaussianRotationVelocity V W u) := by unfold cavityGaussianRotationVelocity; fun_prop
  have hh (u : ℝ) : Measurable (fun p : EuclideanSpace ℝ I×S=>
      H p.2+inner ℝ (cavityGaussianRotation V W u p.2) p.1) :=
    (hH.comp measurable_snd).add (((hv u).comp measurable_snd).inner measurable_fst)
  have hd (u : ℝ) : Measurable (fun p : EuclideanSpace ℝ I×S=>
      inner ℝ (cavityGaussianRotationVelocity V W u p.2) p.1) :=
    ((hw u).comp measurable_snd).inner measurable_fst
  have hm (u : ℝ) : Measurable (fun g=>Real.log (tiltPartition μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1)) :=
    (kernel_tiltPartition_measurable (Kernel.const _ μ) (hh u)).log
  have hmd (u : ℝ) : Measurable (fun g=>tiltMean μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g)
      (fun s=>inner ℝ (cavityGaussianRotationVelocity V W u s) g) 1) :=
    kernel_tiltMean_measurable (Kernel.const _ μ) (hh u) (hd u)
  have hn : Integrable (fun g : EuclideanSpace ℝ I=>‖g‖) (stdGaussian (EuclideanSpace ℝ I)) :=
    ((IsGaussian.memLp_two_id (μ:=stdGaussian (EuclideanSpace ℝ I))).integrable (by norm_num)).norm
  have hb (u : ℝ) (g : EuclideanSpace ℝ I) :
      |Real.log (tiltPartition μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1)|≤A+2*C*‖g‖ :=
    tilt_log_partition_bound μ (hH.add ((hv u).inner measurable_const)) (A:=A+2*C*‖g‖) (by positivity) (fun s=>
      (abs_add_le _ _).trans (add_le_add (hHA s) ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (cavityGaussianRotation_norm hC hVC hWC u s) (norm_nonneg g)))))
  have hi (u : ℝ) : Integrable (fun g=>Real.log (tiltPartition μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1)) (stdGaussian (EuclideanSpace ℝ I)) :=
    ((integrable_const A).add (hn.const_mul (2*C))).mono' (hm u).aestronglyMeasurable
      (ae_of_all _ fun g=>by simpa only [Real.norm_eq_abs,Pi.add_apply] using hb u g)
  have ht := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun u g=>Real.log (tiltPartition μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1))
    (F':=fun u g=>tiltMean μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g)
      (fun s=>inner ℝ (cavityGaussianRotationVelocity V W u s) g) 1)
    (s:=univ) (bound:=fun g : EuclideanSpace ℝ I=>2*C*‖g‖) (x₀:=t)
    (by simp : univ∈𝓝 t) (Eventually.of_forall fun u=>(hm u).aestronglyMeasurable)
    (hi t) (hmd t).aestronglyMeasurable
    (ae_of_all _ fun g u _=>by
      rw [Real.norm_eq_abs]
      exact tiltMean_bound_general μ (hH.add ((hv u).inner measurable_const))
        ((hw u).inner measurable_const) (C:=2*C*‖g‖) (by positivity) (fun s=>(abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (cavityGaussianRotationVelocity_norm hC hVC hWC u s) (norm_nonneg g))))
    (hn.const_mul (2*C)) (ae_of_all _ fun g u _=>
      cavityGaussianRotation_log_derivative μ hH hV hW hA hC hHA hVC hWC g u)
  exact ht.2
omit hH hV hW hA hC hHA hVC hWC in
lemma cavityGaussianRotation_cross_covariance_bound
    {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    {V W : S→EuclideanSpace ℝ I} {ε : ℝ} (_hε : 0≤ε)
    (horth : ∀ x y,inner ℝ (V x) (W y)=0)
    (hcov : ∀ x y,|inner ℝ (W x) (W y)-inner ℝ (V x) (V y)|≤ε)
    (t : ℝ) (x y : S) :
    |inner ℝ (cavityGaussianRotationVelocity V W t x) (cavityGaussianRotation V W t y)|≤ε := by
  have hr : inner ℝ (W x) (V y)=0 := by rw [real_inner_comm,horth]
  have he : inner ℝ (cavityGaussianRotationVelocity V W t x) (cavityGaussianRotation V W t y)=
      Real.sin t*Real.cos t*(inner ℝ (W x) (W y)-inner ℝ (V x) (V y)) := by
    simp only [cavityGaussianRotation,cavityGaussianRotationVelocity,inner_add_left,inner_add_right,
      inner_smul_left,inner_smul_right,conj_trivial,horth,hr]
    ring
  rw [he,abs_mul,abs_mul]
  have h1 : |Real.sin t| * |Real.cos t| ≤ 1 := by
    nlinarith [Real.abs_sin_le_one t,Real.abs_cos_le_one t,abs_nonneg (Real.sin t),abs_nonneg (Real.cos t)]
  exact (mul_le_mul h1 (hcov x y) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul ε)

theorem euclideanGaussian_covariance_comparison {ε : ℝ} (hε : 0≤ε)
    (horth : ∀ x y,inner ℝ (V x) (W y)=0)
    (hcov : ∀ x y,|inner ℝ (W x) (W y)-inner ℝ (V x) (V y)|≤ε) :
    |(∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (W s) g) 1)
        ∂stdGaussian (EuclideanSpace ℝ I))-
      ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)
        ∂stdGaussian (EuclideanSpace ℝ I)|≤Real.pi*ε := by
  let F : ℝ→ℝ:=fun t=>∫ g,Real.log (tiltPartition μ
    (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g) 1) ∂stdGaussian (EuclideanSpace ℝ I)
  let D : ℝ→ℝ:=fun t=>∫ g,tiltMean μ
    (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g)
    (fun s=>inner ℝ (cavityGaussianRotationVelocity V W t s) g) 1 ∂stdGaussian (EuclideanSpace ℝ I)
  have hd (t : ℝ) : HasDerivAt F (D t) t :=
    cavityGaussianRotation_mean_derivative μ hH hV hW hA hC hHA hVC hWC t
  have hb (t : ℝ) : ‖D t‖≤2*ε := by
    have hv : Measurable (cavityGaussianRotation V W t) := by unfold cavityGaussianRotation; fun_prop
    have hw : Measurable (cavityGaussianRotationVelocity V W t) := by unfold cavityGaussianRotationVelocity; fun_prop
    have hc := cavityGaussianRotation_cross_covariance_bound (V:=V) (W:=W) hε horth hcov t
    change ‖∫ g,tiltMean μ _ _ 1 ∂stdGaussian (EuclideanSpace ℝ I)‖≤_
    rw [euclideanGaussian_tiltMean_ibp μ hH hv hw hHA
      (fun x=>pow_le_pow_left₀ (norm_nonneg _) (cavityGaussianRotation_norm hC hVC hWC t x) 2)
      (fun x=>pow_le_pow_left₀ (norm_nonneg _) (cavityGaussianRotationVelocity_norm hC hVC hWC t x) 2)]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=stdGaussian (EuclideanSpace ℝ I)) (C:=2*ε) (ae_of_all _ fun g=>by
        have hh : Measurable (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g) :=
          hH.add (hv.inner measurable_const)
        have h1 := tiltMean_bound_general μ (t:=1) hh (hw.inner hv) hε (fun x=>hc x x)
        have h2 := tiltMean_bound_general (Measure.pi (fun _ : Fin 2=>μ)) (t:=1)
          (replicaPotential_measurable hh 2)
          ((hw.comp (measurable_pi_apply 1)).inner (hv.comp (measurable_pi_apply 0))) hε
          (fun xs=>hc (xs 1) (xs 0))
        rw [Real.norm_eq_abs]
        apply (abs_sub _ _).trans
        exact (add_le_add h1 h2).trans_eq (by ring))
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t∈Icc (0:ℝ) (Real.pi/2))=>(hd t).hasDerivWithinAt)
    (fun t _=>hb t) (convex_Icc (0:ℝ) (Real.pi/2))
    (show (0:ℝ)∈Icc (0:ℝ) (Real.pi/2) by constructor; rfl; positivity)
    (show Real.pi/2∈Icc (0:ℝ) (Real.pi/2) by constructor; positivity; rfl)
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg (by positivity : 0≤Real.pi/2)] at hm
  convert hm using 1
  · simp [F,cavityGaussianRotation]
  · ring
end SphericalPerceptronFreeEnergy
end

end OAI
