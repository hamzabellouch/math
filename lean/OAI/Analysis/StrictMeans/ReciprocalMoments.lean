import OAI.Analysis.StrictMeans.FamilyDerivatives

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

abbrev HalfPlaneSet := {z : ℂ // 0 < z.im}

def reciprocalFunction (f : DiskFamily) (z : ℂ) : ℂ :=
  (deriv (halfPlaneFunction f) z)⁻¹

@[simp] lemma reciprocalFunction_I (f : DiskFamily) : reciprocalFunction f I = 1 := by
  simp [reciprocalFunction]

lemma reciprocalFunction_ne_zero (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    reciprocalFunction f z ≠ 0 :=
  inv_ne_zero (halfPlaneFunction_deriv_ne_zero f hz)

lemma reciprocalFunction_differentiableOn (f : DiskFamily) :
    DifferentiableOn ℂ (reciprocalFunction f) {z : ℂ | 0 < z.im} :=
  ((halfPlaneFunction_differentiableOn f).deriv isOpen_halfPlane).inv
    (fun _ hz => halfPlaneFunction_deriv_ne_zero f hz)

lemma continuous_reciprocalFunction :
    Continuous (fun p : DiskFamily × HalfPlaneSet => reciprocalFunction p.1 p.2) := by
  have hc : Continuous (fun z : HalfPlaneSet => (⟨z, z.property⟩ : UpperHalfPlane)) :=
    continuous_subtype_val.upperHalfPlaneMk (fun z => z.property)
  change Continuous (fun p : DiskFamily × HalfPlaneSet => halfPlaneQ p.1 ⟨p.2, p.2.property⟩)
  have hmap : Continuous (fun p : DiskFamily × HalfPlaneSet =>
      (p.1, (⟨p.2, p.2.property⟩ : UpperHalfPlane))) :=
    continuous_fst.prodMk (hc.comp continuous_snd)
  have hh := continuous_halfPlaneQ.comp hmap
  exact hh

lemma continuous_reciprocalFunction_deriv :
    Continuous (fun p : DiskFamily × HalfPlaneSet => deriv (reciprocalFunction p.1) p.2) :=
  continuous_holomorphicFamily_deriv isOpen_halfPlane _ continuous_reciprocalFunction
    reciprocalFunction_differentiableOn

lemma continuous_reciprocalFunction_deriv₂ :
    Continuous (fun p : DiskFamily × HalfPlaneSet => deriv (deriv (reciprocalFunction p.1)) p.2) :=
  continuous_holomorphicFamily_deriv isOpen_halfPlane _ continuous_reciprocalFunction_deriv
    (fun f => (reciprocalFunction_differentiableOn f).deriv isOpen_halfPlane)

abbrev MomentInterval := Set.Icc (-(1 / 2) : ℝ) (1 / 2)

def sourcePath (v : ℂ) (t : ℝ) : ℂ := I + (t : ℂ) * v

@[simp] lemma sourcePath_zero (v : ℂ) : sourcePath v 0 = I := by simp [sourcePath]

lemma sourcePath_mem (v : ℂ) (hv : |v.im| ≤ 1) {t : ℝ} (ht : t ∈ MomentInterval) :
    0 < (sourcePath v t).im := by
  have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
  have hm : |t * v.im| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |t| * |v.im| ≤ (1 / 2) * 1 := mul_le_mul ht' hv (abs_nonneg _) (by norm_num)
         _ = 1 / 2 := by ring
  have hh := (abs_le.mp hm).1
  simp only [sourcePath, add_im, mul_im, I_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  linarith

lemma sourcePath_hasDerivAt (v : ℂ) (t : ℝ) : HasDerivAt (sourcePath v) v t := by
  have hf : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using! Complex.ofRealCLM.hasDerivAt (x := t)
  change HasDerivAt (fun s : ℝ => I + (s : ℂ) * v) v t
  simpa only [one_mul] using (hf.mul_const v).const_add I

lemma continuous_sourcePath (v : ℂ) : Continuous (sourcePath v) := by
  unfold sourcePath
  fun_prop

lemma reciprocalPath_hasDerivAt (f : DiskFamily) (v : ℂ) {t : ℝ}
    (ht : 0 < (sourcePath v t).im) :
    HasDerivAt (fun t => reciprocalFunction f (sourcePath v t))
      (deriv (reciprocalFunction f) (sourcePath v t) * v) t := by
  have h := ((reciprocalFunction_differentiableOn f).differentiableAt
    (isOpen_halfPlane.mem_nhds ht)).hasDerivAt.scomp t (sourcePath_hasDerivAt v t)
  simpa only [smul_eq_mul, mul_comm] using! h

lemma reciprocalPath_deriv_hasDerivAt (f : DiskFamily) (v : ℂ) {t : ℝ}
    (ht : 0 < (sourcePath v t).im) :
    HasDerivAt (fun t => deriv (reciprocalFunction f) (sourcePath v t) * v)
      (deriv (deriv (reciprocalFunction f)) (sourcePath v t) * v ^ 2) t := by
  have h := (((reciprocalFunction_differentiableOn f).deriv isOpen_halfPlane).differentiableAt
    (isOpen_halfPlane.mem_nhds ht)).hasDerivAt.scomp t (sourcePath_hasDerivAt v t)
  have hh : HasDerivAt (fun t => deriv (reciprocalFunction f) (sourcePath v t) * v)
      ((v * deriv (deriv (reciprocalFunction f)) (sourcePath v t)) * v) t := by
    simpa only [Function.comp_def, smul_eq_mul] using! h.mul_const v
  convert hh using 1
  ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

def normPathFirst (f : DiskFamily) (v : ℂ) (t : ℝ) : ℝ :=
  (conj (reciprocalFunction f (sourcePath v t)) *
    (deriv (reciprocalFunction f) (sourcePath v t) * v)).re /
    ‖reciprocalFunction f (sourcePath v t)‖

def normPathSecond (f : DiskFamily) (v : ℂ) (t : ℝ) : ℝ :=
  ((conj (deriv (reciprocalFunction f) (sourcePath v t) * v) *
    (deriv (reciprocalFunction f) (sourcePath v t) * v) +
    conj (reciprocalFunction f (sourcePath v t)) *
    (deriv (deriv (reciprocalFunction f)) (sourcePath v t) * v ^ 2)).re) /
    ‖reciprocalFunction f (sourcePath v t)‖ -
  ((conj (reciprocalFunction f (sourcePath v t)) *
    (deriv (reciprocalFunction f) (sourcePath v t) * v)).re) ^ 2 /
    ‖reciprocalFunction f (sourcePath v t)‖ ^ 3

lemma normPath_hasDerivAt (f : DiskFamily) (v : ℂ) {t : ℝ}
    (ht : 0 < (sourcePath v t).im) :
    HasDerivAt (fun t => ‖reciprocalFunction f (sourcePath v t)‖) (normPathFirst f v t) t :=
  complex_path_norm_hasDerivAt (reciprocalPath_hasDerivAt f v ht)
    (reciprocalFunction_ne_zero f ht)

lemma normPathFirst_hasDerivAt (f : DiskFamily) (v : ℂ) {t : ℝ}
    (ht : 0 < (sourcePath v t).im) :
    HasDerivAt (normPathFirst f v) (normPathSecond f v t) t :=
  complex_path_normFirst_hasDerivAt (reciprocalPath_hasDerivAt f v ht)
    (reciprocalPath_deriv_hasDerivAt f v ht) rfl (reciprocalFunction_ne_zero f ht)

lemma continuous_normPath_on_interval (v : ℂ) (hv : |v.im| ≤ 1) :
    Continuous (fun p : DiskFamily × MomentInterval =>
      ‖reciprocalFunction p.1 (sourcePath v p.2)‖) ∧
    Continuous (fun p : DiskFamily × MomentInterval => normPathFirst p.1 v p.2) ∧
    Continuous (fun p : DiskFamily × MomentInterval => normPathSecond p.1 v p.2) := by
  let m : DiskFamily × MomentInterval → DiskFamily × HalfPlaneSet :=
    fun p => (p.1, ⟨sourcePath v p.2, sourcePath_mem v hv p.2.property⟩)
  have hm : Continuous m := continuous_fst.prodMk
    (((continuous_sourcePath v).comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
  have h₀ := continuous_reciprocalFunction.comp hm
  have h₁ := (continuous_reciprocalFunction_deriv.comp hm).mul_const v
  have h₂ := (continuous_reciprocalFunction_deriv₂.comp hm).mul_const (v ^ 2)
  have hn : ∀ p : DiskFamily × MomentInterval,
      ‖reciprocalFunction p.1 (sourcePath v p.2)‖ ≠ 0 :=
    fun p => norm_ne_zero_iff.mpr (reciprocalFunction_ne_zero _ (sourcePath_mem v hv p.2.property))
  refine ⟨h₀.norm, ?_, ?_⟩
  · exact (Complex.continuous_re.comp ((Complex.continuous_conj.comp h₀).mul h₁)).div h₀.norm hn
  · exact (Complex.continuous_re.comp (((Complex.continuous_conj.comp h₁).mul h₁).add ((Complex.continuous_conj.comp h₀).mul h₂))).div h₀.norm hn |>.sub
      (((Complex.continuous_re.comp ((Complex.continuous_conj.comp h₀).mul h₁)).pow 2).div (h₀.norm.pow 3) (fun p => pow_ne_zero _ (hn p)))

@[simp] lemma normPathFirst_zero (f : DiskFamily) (v : ℂ) :
    normPathFirst f v 0 = (deriv (reciprocalFunction f) I * v).re := by
  simp [normPathFirst]

@[simp] lemma normPathSecond_zero (f : DiskFamily) (v : ℂ) :
    normPathSecond f v 0 = (deriv (deriv (reciprocalFunction f)) I * v ^ 2).re +
      (deriv (reciprocalFunction f) I * v).im ^ 2 := by
  unfold normPathSecond
  rw [sourcePath_zero, reciprocalFunction_I]
  exact complex_normSecond_at_one _ _

lemma normPathSecond_add_axes (f : DiskFamily) :
    normPathSecond f 1 0 + normPathSecond f I 0 = ‖deriv (reciprocalFunction f) I‖ ^ 2 := by
  rw [normPathSecond_zero, normPathSecond_zero, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, mul_im, Complex.I_sq]
  ring

lemma normPath_integral_hasDerivAt (μ : Measure DiskFamily) [IsFiniteMeasure μ]
    (v : ℂ) (hv : |v.im| ≤ 1) {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    HasDerivAt (fun t => ∫ f, ‖reciprocalFunction f (sourcePath v t)‖ ∂μ)
      (∫ f, normPathFirst f v t ∂μ) t := by
  have hc := continuous_normPath_on_interval v hv
  exact compactFamily_hasDerivAt_integral μ isCompact_Icc (Icc_mem_nhds ht.1 ht.2) hc.1 hc.2.1
    (fun f t htt => normPath_hasDerivAt f v (sourcePath_mem v hv htt))

lemma normPathFirst_integral_hasDerivAt (μ : Measure DiskFamily) [IsFiniteMeasure μ]
    (v : ℂ) (hv : |v.im| ≤ 1) {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    HasDerivAt (fun t => ∫ f, normPathFirst f v t ∂μ)
      (∫ f, normPathSecond f v t ∂μ) t := by
  have hc := continuous_normPath_on_interval v hv
  exact compactFamily_hasDerivAt_integral μ isCompact_Icc (Icc_mem_nhds ht.1 ht.2) hc.2.1 hc.2.2
    (fun f t htt => normPathFirst_hasDerivAt f v (sourcePath_mem v hv htt))

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

def ReciprocalMeanLaw (μ : Measure DiskFamily) (β : ℝ) : Prop :=
  ∀ z : UpperHalfPlane, (∫ f, ‖reciprocalFunction f z‖ ∂μ) = z.im ^ (-β)

lemma affine_real_law_mean_law (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, affineOperator z φ f ∂(μ : Measure DiskFamily)) =
        z.im ^ (-β) * ∫ f, φ f ∂(μ : Measure DiskFamily)) :
    ReciprocalMeanLaw (μ : Measure DiskFamily) β := by
  intro z
  have h := hlaw z 1
  simpa [affineOperator_apply, reciprocalFunction, halfPlaneQ] using h

lemma normPath_integral_eq_rpow (μ : Measure DiskFamily) (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) (v : ℂ) (hv : |v.im| ≤ 1)
    {t : ℝ} (ht : t ∈ MomentInterval) :
    (∫ f, ‖reciprocalFunction f (sourcePath v t)‖ ∂μ) = (1 + t * v.im) ^ (-β) := by
  have h := hlaw ⟨sourcePath v t, sourcePath_mem v hv ht⟩
  simpa [UpperHalfPlane.im, sourcePath] using h

lemma normPathFirst_integral_eq (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) (v : ℂ) (hv : |v.im| ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    (∫ f, normPathFirst f v t ∂μ) = v.im * (-β) * (1 + t * v.im) ^ (-β - 1) := by
  have hp : 0 < 1 + t * v.im := by
    simpa [sourcePath] using sourcePath_mem v hv (show t ∈ MomentInterval from ⟨ht.1.le, ht.2.le⟩)
  have hh := normPath_integral_hasDerivAt μ v hv ht
  have he : (fun t => (1 + t * v.im) ^ (-β)) =ᶠ[𝓝 t]
      (fun t => ∫ f, ‖reciprocalFunction f (sourcePath v t)‖ ∂μ) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact (normPath_integral_eq_rpow μ β hlaw v hv hs).symm
  have hp' := (((hasDerivAt_id t).mul_const v.im).const_add 1).rpow_const (p := -β) (Or.inl hp.ne')
  have hpow : HasDerivAt (fun s => (1 + s * v.im) ^ (-β))
      (v.im * (-β) * (1 + t * v.im) ^ (-β - 1)) t := by
    simpa only [one_mul, id_eq] using! hp'
  exact (hh.congr_of_eventuallyEq he).unique hpow

lemma normPathFirst_integral_zero (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) (v : ℂ) (hv : |v.im| ≤ 1) :
    (∫ f, (deriv (reciprocalFunction f) I * v).re ∂μ) = -β * v.im := by
  simpa [mul_comm] using normPathFirst_integral_eq μ β hlaw v hv (t := 0) (by norm_num)

lemma normPathSecond_integral_zero (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) (v : ℂ) (hv : |v.im| ≤ 1) :
    (∫ f, normPathSecond f v 0 ∂μ) = v.im ^ 2 * β * (β + 1) := by
  have hh := normPathFirst_integral_hasDerivAt μ v hv (t := 0) (by norm_num)
  have he : (fun t => v.im * (-β) * (1 + t * v.im) ^ (-β - 1)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∫ f, normPathFirst f v t ∂μ) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
    exact (normPathFirst_integral_eq μ β hlaw v hv ht).symm
  have hp := (((hasDerivAt_id (0 : ℝ)).mul_const v.im).const_add 1).rpow_const
    (p := -β - 1) (Or.inl (by norm_num))
  have hp' := hp.const_mul (v.im * (-β))
  have hpow : HasDerivAt (fun t => v.im * (-β) * (1 + t * v.im) ^ (-β - 1))
      (v.im ^ 2 * β * (β + 1)) 0 := by
    convert! hp' using 1
    simp only [id_eq, one_mul, zero_mul, add_zero, Real.one_rpow, mul_one]
    ring
  exact (hh.congr_of_eventuallyEq he).unique hpow

lemma normPathSecond_integrable_zero (μ : Measure DiskFamily) [IsFiniteMeasure μ]
    (v : ℂ) (hv : |v.im| ≤ 1) : Integrable (fun f => normPathSecond f v 0) μ := by
  have hc := (continuous_normPath_on_interval v hv).2.2.comp
    (continuous_id.prodMk (continuous_const (y := (⟨0, by norm_num⟩ : MomentInterval))))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma reciprocal_deriv_norm_sq_moment (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) :
    (∫ f, ‖deriv (reciprocalFunction f) I‖ ^ 2 ∂μ) = β * (β + 1) := by
  simp_rw [← normPathSecond_add_axes]
  rw [integral_add (normPathSecond_integrable_zero μ 1 (by simp))
    (normPathSecond_integrable_zero μ I (by simp)),
    normPathSecond_integral_zero μ β hlaw 1 (by simp),
    normPathSecond_integral_zero μ β hlaw I (by simp)]
  simp

end
end StrictInverseFirstPower

end

end OAI
