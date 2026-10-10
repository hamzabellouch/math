import Mathlib

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def rationalKernel (r : ℝ) (z : V) : ℝ := r^4/(r^2+‖z‖^2)^3

omit [InnerProductSpace ℝ V] in
lemma rationalKernel_nonneg (r : ℝ) (z : V) : 0 ≤ rationalKernel r z := by
  unfold rationalKernel
  positivity

omit [InnerProductSpace ℝ V] in
lemma rationalKernel_pos {r : ℝ} (hr : 0 < r) (z : V) : 0 < rationalKernel r z := by
  unfold rationalKernel
  positivity

lemma rationalKernel_smooth {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (rationalKernel (V := V) r) := by
  unfold rationalKernel
  exact contDiff_const.div ((contDiff_const.add (contDiff_norm_sq ℝ)).pow 3)
    (fun z => by positivity)

lemma rationalKernel_deriv {r : ℝ} (hr : 0 < r) (z v : V) :
    fderiv ℝ (rationalKernel r) z v =
      -(6*r^4/(r^2+‖z‖^2)^4)*⟪z,v⟫ := by
  have hd : r^2+‖z‖^2 ≠ 0 := ne_of_gt (by positivity)
  have hh₀ := (hasDerivAt_const (‖z‖^2) (r^4)).div
    (((hasDerivAt_id (‖z‖^2)).const_add (r^2)).pow 3) (pow_ne_zero _ hd)
  have hh := hh₀.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  change HasFDerivAt (rationalKernel r) _ z at hh
  rw [hh.fderiv]
  simp only [smul_apply, smul_eq_mul, Pi.pow_apply, id_eq, innerSL_apply_apply]
  field_simp
  ring

omit [InnerProductSpace ℝ V] in
lemma rationalKernel_neg (r : ℝ) (z : V) : rationalKernel r (-z) = rationalKernel r z := by
  simp [rationalKernel]

omit [InnerProductSpace ℝ V] in
lemma compact_continuous_bound {W : Type*} [NormedAddCommGroup W]
    (f : V → W) (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C := by
  obtain ⟨C,hC⟩ := hs.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun z => ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact (hC z hz).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz,norm_zero]
    exact le_max_right _ _

section Measure
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

lemma hasFDerivAt_finite_convolution (μ : Measure V) [IsFiniteMeasure μ]
    (k : V → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (x : V) :
    HasFDerivAt (fun x => ∫ y, k (x-y) ∂μ)
      (∫ y, fderiv ℝ k (x-y) ∂μ) x := by
  have hd : Continuous (fderiv ℝ k) := hk.continuous_fderiv (by simp)
  obtain ⟨C,_,hC⟩ := compact_continuous_bound k hk.continuous hc
  obtain ⟨D,_,hD⟩ := compact_continuous_bound (fderiv ℝ k) hd (hc.fderiv ℝ)
  have hm (a : V) : Continuous (fun y => k (a-y)) := hk.continuous.comp (continuous_const.sub continuous_id)
  have hdm (a : V) : Continuous (fun y => fderiv ℝ k (a-y)) := hd.comp (continuous_const.sub continuous_id)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := fun _ => D)
    (Filter.univ_mem) (Eventually.of_forall (fun a => (hm a).aestronglyMeasurable))
    ((integrable_const C).mono' (hm x).aestronglyMeasurable (Eventually.of_forall (fun y => hC (x-y))))
    (hdm x).aestronglyMeasurable (Eventually.of_forall (fun y a _ => hD (a-y)))
    (integrable_const D)
  apply Eventually.of_forall
  intro y a _
  simpa only [Function.comp_def,ContinuousLinearMap.comp_id,id_eq] using ((hk.differentiable (by simp)).differentiableAt (x := a-y)).hasFDerivAt.comp a
    ((hasFDerivAt_id a).sub_const y)

lemma finite_convolution_deriv (μ : Measure V) [IsFiniteMeasure μ]
    (k : V → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (x v : V) :
    fderiv ℝ (fun x => ∫ y, k (x-y) ∂μ) x v = ∫ y, fderiv ℝ k (x-y) v ∂μ := by
  rw [(hasFDerivAt_finite_convolution μ k hk hc x).fderiv]
  apply ContinuousLinearMap.integral_apply
  have hd : Continuous (fderiv ℝ k) := hk.continuous_fderiv (by simp)
  obtain ⟨D,_,hD⟩ := compact_continuous_bound (fderiv ℝ k) hd (hc.fderiv ℝ)
  exact (integrable_const D).mono'
    (hd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall (fun y => hD (x-y)))

omit [SecondCountableTopology V] in
lemma finite_convolution_smooth (μ : Measure V) [IsFiniteMeasure μ]
    (k : V → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ContDiff ℝ ∞ (fun x => ∫ y, k (x-y) ∂μ) := by
  have hh := hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    ((integrable_const (1:ℝ)).locallyIntegrable (μ := μ)) hk
  have he : convolution (fun _ : V => (1:ℝ)) k (ContinuousLinearMap.mul ℝ ℝ) μ =
      (fun x => ∫ y, k (x-y) ∂μ) := by
    funext x
    simp only [convolution_def,ContinuousLinearMap.mul_apply',one_mul]
  rw [he] at hh
  exact hh

end Measure

def cutKernel (η : V → ℝ) (r : ℝ) (z : V) : ℝ := η z*rationalKernel r z

lemma cutKernel_smooth {r : ℝ} (hr : 0 < r) (η : V → ℝ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (cutKernel η r) := hη.mul (rationalKernel_smooth hr)

omit [InnerProductSpace ℝ V] in
lemma cutKernel_compact (η : V → ℝ) (hη : HasCompactSupport η) (r : ℝ) :
    HasCompactSupport (cutKernel η r) := hη.mul_right

lemma cutKernel_deriv {r : ℝ} (hr : 0 < r) (η : V → ℝ) (hη : ContDiff ℝ ∞ η) (z v : V) :
    fderiv ℝ (cutKernel η r) z v =
      (fderiv ℝ η z v)*rationalKernel r z -
        η z*(6*r^4/(r^2+‖z‖^2)^4)*⟪z,v⟫ := by
  have h₁ := ((hη.differentiable (by simp)).differentiableAt (x := z)).hasFDerivAt
  have h₂ := (((rationalKernel_smooth hr).differentiable (by simp)).differentiableAt (x := z)).hasFDerivAt
  change fderiv ℝ (η * rationalKernel r) z v = _
  rw [(h₁.mul h₂).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,
    rationalKernel_deriv hr]
  ring
end TamingCompatibility.Concentration

end
end

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace TamingCompatibility.Concentration

def radialCoefficient (r t : ℝ) : ℝ := r^4/(r^2+t^2)^4

lemma radialCoefficient_nonneg (r t : ℝ) : 0 ≤ radialCoefficient r t := by
  unfold radialCoefficient
  positivity

lemma rational_cutoff_bound (r t : ℝ) : radialCoefficient r t*t^4 ≤ 1 := by
  unfold radialCoefficient
  by_cases hz : r^2+t^2 = 0
  · simp [hz]
  have hh : (r*t)^2 ≤ (r^2+t^2)^2 := by nlinarith [sq_nonneg (r-t),sq_nonneg (r+t)]
  have h4 : r^4*t^4 ≤ (r^2+t^2)^4 := by nlinarith [sq_nonneg ((r^2+t^2)^2-(r*t)^2)]
  rw [div_mul_eq_mul_div]
  exact (div_le_one (pow_pos (lt_of_le_of_ne (by positivity) (Ne.symm hz)) 4)).mpr h4

lemma radialCoefficient_mul_defect_bound {r t d : ℝ} (hd : 0 ≤ d) (hz : t = 0 → d = 0) :
    radialCoefficient r t*d ≤ d/t^4 := by
  by_cases ht : t = 0
  · simp [hz ht]
  have ht4 : 0 < t^4 := lt_of_le_of_ne (by positivity) (Ne.symm (pow_ne_zero 4 ht))
  apply (le_div_iff₀ ht4).mpr
  have hh := mul_le_mul_of_nonneg_right (rational_cutoff_bound r t) hd
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma rational_defect_tendsto_zero (D t : Ω → ℝ) (hD : Measurable D) (ht : Measurable t)
    (hDp : ∀ x, 0 ≤ D x) (hzero : ∀ x, t x = 0 → D x = 0)
    (hint : Integrable (fun x => D x/(t x)^4) μ) :
    Tendsto (fun r : ℝ => ∫ x, radialCoefficient r (t x)*D x ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hm (r : ℝ) : Measurable (fun x => radialCoefficient r (t x)*D x) :=
    (measurable_const.div ((measurable_const.add (ht.pow_const 2)).pow_const 4)).mul hD
  have hb (r : ℝ) (x : Ω) : ‖radialCoefficient r (t x)*D x‖ ≤ D x/(t x)^4 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (radialCoefficient_nonneg _ _) (hDp x))]
    exact radialCoefficient_mul_defect_bound (hDp x) (hzero x)
  have hl (x : Ω) : Tendsto (fun r : ℝ => radialCoefficient r (t x)*D x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    by_cases hx : t x = 0
    · simp only [hzero x hx,mul_zero]
      exact tendsto_const_nhds
    · have h4 : Tendsto (fun r : ℝ => r^4) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        simpa using (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.pow 4) :
          Tendsto (fun r : ℝ => r^4) (𝓝[>] (0:ℝ)) (𝓝 ((0:ℝ)^4)))
      have h2 : Tendsto (fun r : ℝ => r^2+(t x)^2) (𝓝[>] (0:ℝ)) (𝓝 ((t x)^2)) := by
        simpa using ((tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.pow 2)).add
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (t x)^2) (𝓝[>] (0:ℝ)) (𝓝 ((t x)^2))) :
          Tendsto (fun r : ℝ => r^2+(t x)^2) (𝓝[>] (0:ℝ)) (𝓝 ((0:ℝ)^2+(t x)^2)))
      have hh := (h4.div (h2.pow 4) (pow_ne_zero 4 (pow_ne_zero 2 hx))).mul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => D x) (𝓝[>] (0:ℝ)) (𝓝 (D x)))
      simpa only [radialCoefficient,Pi.div_apply,zero_div,zero_mul] using hh
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (fun x => D x/(t x)^4) (Eventually.of_forall (fun r => (hm r).aestronglyMeasurable))
    (Eventually.of_forall (fun r => Eventually.of_forall (hb r))) hint (Eventually.of_forall hl)

lemma rational_geometric_error_tendsto_zero [IsFiniteMeasure μ] (t : Ω → ℝ) (ht : Measurable t) :
    Tendsto (fun r : ℝ => ∫ x, radialCoefficient r (t x)*(t x)^4 ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply rational_defect_tendsto_zero _ t (ht.pow_const 4) ht (fun x => by positivity)
    (fun x hx => by simp [hx])
  apply (integrable_const (1:ℝ)).mono' ((ht.pow_const 4).div (ht.pow_const 4)).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  by_cases hx : t x = 0 <;> simp [hx]
end TamingCompatibility.Concentration

end
end

end OAI
