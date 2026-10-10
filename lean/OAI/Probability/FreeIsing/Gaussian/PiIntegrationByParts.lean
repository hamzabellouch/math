import OAI.Probability.FreeIsing.Gaussian.IntegrationByParts

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

section CoordinateSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurePreserving_funSplitAt (μ : ι → Measure ℝ)
    [∀ j, SigmaFinite (μ j)] (i : ι) :
    MeasurePreserving (Homeomorph.funSplitAt ℝ i) (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j : {j // j ≠ i} => μ j)) := by
  let e := (Homeomorph.funSplitAt ℝ i).toMeasurableEquiv.symm
  apply MeasurePreserving.symm e
  refine ⟨e.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [e.map_apply]
  have hpre : e ⁻¹' Set.pi Set.univ s =
      s i ×ˢ Set.pi Set.univ (fun j : {j // j ≠ i} => s j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_prod]
    constructor
    · intro h
      constructor
      · simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt] using h i
      · intro j
        simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt, j.property] using h j
    · rintro ⟨hi, hj⟩ j
      by_cases hji : j = i
      · subst j
        simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt] using hi
      · simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt, hji] using hj ⟨j, hji⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  simpa using (Fintype.prod_eq_mul_prod_subtype_ne (fun j => μ j (s j)) i).symm

theorem gaussian_pi_integral_centered_mul_of_bounded_deriv
    (m : ι → ℝ) (v : ι → ℝ≥0) (i : ι)
    {f f' : (ι → ℝ) → ℝ} {C D : ℝ}
    (hfc : Continuous f) (hf'c : Continuous f')
    (hf : ∀ z t, HasDerivAt (fun r => f (Function.update z i r))
      (f' (Function.update z i t)) t)
    (hbound : ∀ z, |f z| ≤ C) (hbound' : ∀ z, |f' z| ≤ D) :
    (∫ z, (z i - m i) * f z ∂Measure.pi (fun j => gaussianReal (m j) (v j))) =
      (v i : ℝ) * ∫ z, f' z ∂Measure.pi (fun j => gaussianReal (m j) (v j)) := by
  let μ : ι → Measure ℝ := fun j => gaussianReal (m j) (v j)
  let ν := Measure.pi (fun j : {j // j ≠ i} => μ j)
  let e := (Homeomorph.funSplitAt ℝ i).toMeasurableEquiv.symm
  have hmp : MeasurePreserving e ((μ i).prod ν) (Measure.pi μ) :=
    (measurePreserving_funSplitAt μ i).symm
  have heval (x : ℝ × ({j // j ≠ i} → ℝ)) : e x i = x.1 := by
    simp [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt, Equiv.piSplitAt]
  have hupdate (x : ℝ × ({j // j ≠ i} → ℝ)) (t : ℝ) :
      Function.update (e x) i t = e (t, x.2) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [heval]
    · simp [e, Homeomorph.funSplitAt,
        Homeomorph.piSplitAt, Equiv.piSplitAt, hji]
  have hxi : Integrable (fun z : ι → ℝ => z i - m i) (Measure.pi μ) := by
    have hi : Integrable (fun r : ℝ => r - m i) (μ i) :=
      ((memLp_id_gaussianReal 1).integrable (by norm_num)).sub (integrable_const _)
    exact (measurePreserving_eval μ i).integrable_comp_of_integrable hi
  have hxfi : Integrable (fun z : ι → ℝ => (z i - m i) * f z) (Measure.pi μ) :=
    hxi.mul_bdd hfc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hbound z)
  have hf'i : Integrable f' (Measure.pi μ) :=
    Integrable.of_bound hf'c.aestronglyMeasurable D
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hbound' z)
  have hprod := (hmp.integrable_comp_emb e.measurableEmbedding).2 hxfi
  have hprod' := (hmp.integrable_comp_emb e.measurableEmbedding).2 hf'i
  have hstein (y : {j // j ≠ i} → ℝ) :
      (∫ r, (r - m i) * f (e (r, y)) ∂μ i) =
        (v i : ℝ) * ∫ r, f' (e (r, y)) ∂μ i := by
    apply gaussian_integral_centered_mul_of_bounded_deriv (m i) (v i)
    · intro r
      simpa only [hupdate] using hf (e (0, y)) r
    · exact fun r => hbound _
    · exact fun r => hbound' _
  calc
    _ = ∫ x, (e x i - m i) * f (e x) ∂(μ i).prod ν :=
      (hmp.integral_comp e.measurableEmbedding _).symm
    _ = ∫ y, ∫ r, (r - m i) * f (e (r, y)) ∂μ i ∂ν := by
      simpa only [Function.comp_def, heval] using integral_prod_symm _ hprod
    _ = ∫ y, (v i : ℝ) * ∫ r, f' (e (r, y)) ∂μ i ∂ν := by
      congr 1
      funext y
      exact hstein y
    _ = (v i : ℝ) * ∫ x, f' (e x) ∂(μ i).prod ν := by
      rw [integral_const_mul]
      congr 1
      exact (integral_prod_symm _ hprod').symm
    _ = _ := by rw [hmp.integral_comp e.measurableEmbedding]

theorem gaussian_pi_integral_mul_affine_of_bounded_deriv
    (a b : ι → ℝ) (i : ι)
    {f f' : (ι → ℝ) → ℝ} {C D : ℝ}
    (hfc : Continuous f) (hf'c : Continuous f')
    (hf : ∀ z t, HasDerivAt (fun r => f (Function.update z i r))
      (f' (Function.update z i t)) t)
    (hbound : ∀ z, |f z| ≤ C) (hbound' : ∀ z, |f' z| ≤ D) :
    (∫ z, z i * f (fun j => a j + b j * z j)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      b i * ∫ z, f' (fun j => a j + b j * z j)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let A : (ι → ℝ) → (ι → ℝ) := fun z j => a j + b j * z j
  have hAc : Continuous A := continuous_pi fun j =>
    continuous_const.add (continuous_const.mul (continuous_apply j))
  have hupdate (z : ι → ℝ) (t : ℝ) :
      A (Function.update z i t) = Function.update (A z) i (a i + b i * t) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [A]
    · simp [A, hji]
  have hd (z : ι → ℝ) (t : ℝ) :
      HasDerivAt (fun r => f (A (Function.update z i r)))
        (b i * f' (A (Function.update z i t))) t := by
    simp only [hupdate]
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
      (hf (A z) (a i + b i * t)).comp t
        (((hasDerivAt_id t).const_mul (b i)).const_add (a i))
  have hb' (z : ι → ℝ) : |b i * f' (A z)| ≤ |b i| * D := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbound' _) (abs_nonneg _)
  have h := gaussian_pi_integral_centered_mul_of_bounded_deriv
    (fun _ => 0) (fun _ => 1) i (hfc.comp hAc)
    (continuous_const.mul (hf'c.comp hAc)) hd
    (fun z => hbound (A z)) hb'
  simpa only [Function.comp_def, Pi.mul_apply, A, sub_zero, NNReal.coe_one,
    one_mul, integral_const_mul] using h

theorem gaussian_pi_integral_centered_mul_fderiv
    (m : ι → ℝ) (v : ι → ℝ≥0) (i : ι)
    {f : (ι → ℝ) → ℝ} {C D : ℝ}
    (hf : ContDiff ℝ 1 f) (hbound : ∀ z, |f z| ≤ C)
    (hbound' : ∀ z, |fderiv ℝ f z (Pi.single i 1)| ≤ D) :
    (∫ z, (z i - m i) * f z ∂Measure.pi (fun j => gaussianReal (m j) (v j))) =
      (v i : ℝ) * ∫ z, fderiv ℝ f z (Pi.single i 1)
        ∂Measure.pi (fun j => gaussianReal (m j) (v j)) := by
  apply gaussian_pi_integral_centered_mul_of_bounded_deriv m v i hf.continuous
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    _ hbound hbound'
  intro z t
  exact ((hf.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_update z i t)

theorem gaussian_pi_integral_mul_affine_fderiv
    (a b : ι → ℝ) (i : ι)
    {f : (ι → ℝ) → ℝ} {C D : ℝ}
    (hf : ContDiff ℝ 1 f) (hbound : ∀ z, |f z| ≤ C)
    (hbound' : ∀ z, |fderiv ℝ f z (Pi.single i 1)| ≤ D) :
    (∫ z, z i * f (fun j => a j + b j * z j)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      b i * ∫ z, fderiv ℝ f (fun j => a j + b j * z j) (Pi.single i 1)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  apply gaussian_pi_integral_mul_affine_of_bounded_deriv a b i hf.continuous
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    _ hbound hbound'
  intro z t
  exact ((hf.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_update z i t)

end CoordinateSplit

end Problem367

end

end OAI
