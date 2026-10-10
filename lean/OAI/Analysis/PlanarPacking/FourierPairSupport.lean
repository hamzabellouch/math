import OAI.Analysis.PlanarPacking.Entire
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

open MeasureTheory ComplexConjugate
open scoped FourierTransform RealInnerProductSpace

open scoped FourierTransform RealInnerProductSpace

namespace SharpPlanar


noncomputable def gaussianCoeff (t : ℝ) : ℂ :=
  (Real.pi : ℂ) * b * ((h : ℂ) - Complex.I*t)

noncomputable def spectralGaussian (t : ℝ) (x : Plane) : ℂ :=
  Complex.exp (-gaussianCoeff t * (‖x‖ : ℂ)^2)

lemma gaussianCoeff_re (t : ℝ) : (gaussianCoeff t).re = Real.pi*b*h := by
  simp [gaussianCoeff]

lemma gaussianCoeff_re_pos (t : ℝ) : 0 < (gaussianCoeff t).re := by
  rw [gaussianCoeff_re]
  exact mul_pos (mul_pos Real.pi_pos b_pos) h_pos

lemma spectralGaussian_norm (t : ℝ) (x : Plane) :
    ‖spectralGaussian t x‖ = Real.exp (-Real.pi*b*h*‖x‖^2) := by
  rw [spectralGaussian, Complex.norm_exp]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, gaussianCoeff_re]
  congr 1
  ring

lemma spectralGaussian_continuous : Continuous (fun q : Plane × ℝ => spectralGaussian q.2 q.1) := by
  unfold spectralGaussian gaussianCoeff
  fun_prop

lemma poisson_gaussian_plane {a : ℂ} (ha : 0 < a.re) (ξ : Plane) :
    𝓕 (fun x : Plane => Complex.exp (-a * (‖x‖ : ℂ)^2)) ξ =
      (Real.pi : ℂ)/a * Complex.exp (-(Real.pi : ℂ)^2 * (‖ξ‖ : ℂ)^2/a) := by
  simpa [Plane, finrank_euclideanSpace_fin] using fourier_gaussian_innerProductSpace ha ξ

lemma gaussianCoeff_ne (t : ℝ) : gaussianCoeff t ≠ 0 := by
  intro he
  have := gaussianCoeff_re_pos t
  simp [he] at this

lemma gaussianCoeff_lambda (t : ℝ) : (Real.pi : ℂ)/gaussianCoeff t = lambda t := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have ht := denominator_ne t
  apply (div_eq_iff (gaussianCoeff_ne t)).mpr
  unfold gaussianCoeff lambda
  field_simp [mul_ne_zero hb ht, ht, hb]
  ring_nf
  simp [Complex.I_sq]

lemma z_lambda_relation (t : ℝ) : Complex.I*z t - h = -lambda t/b := by
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have ht := denominator_ne t
  have hbB : (b : ℂ)^2*(B : ℂ) = 1 := by
    rw [B_eq_inv_b_sq]
    push_cast
    exact mul_inv_cancel₀ (pow_ne_zero 2 hb)
  unfold z lambda
  field_simp [ht, hb, mul_ne_zero hb ht]
  ring_nf
  simp only [Complex.I_sq]
  linear_combination (norm := skip) -Complex.I * hbB
  ring_nf
  simp

lemma gaussianCoeff_exponent (t r : ℝ) :
    -(Real.pi : ℂ)^2 * (r : ℂ)^2 / gaussianCoeff t =
      -(Real.pi : ℂ)*h*(b*r^2) + Complex.I*Real.pi*z t*(b*r^2) := by
  have hlam := gaussianCoeff_lambda t
  have hz := z_lambda_relation t
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  calc
    _ = -(Real.pi : ℂ) * (r : ℂ)^2 * lambda t := by rw [← hlam]; ring
    _ = ((Complex.I*z t - h)*b)*Real.pi*r^2 := by rw [hz]; field_simp
    _ = _ := by ring

lemma spectralGaussian_fourier (t : ℝ) (ξ : Plane) :
    𝓕 (spectralGaussian t) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) *
        kernelMoment 0 (b*‖ξ‖^2) t := by
  change 𝓕 (fun x : Plane => Complex.exp (-gaussianCoeff t * (‖x‖ : ℂ)^2)) ξ = _
  rw [poisson_gaussian_plane (gaussianCoeff_re_pos t), gaussianCoeff_lambda,
    gaussianCoeff_exponent]
  unfold kernelMoment
  simp only [pow_zero, mul_one]
  rw [Complex.ofReal_exp, Complex.exp_add]
  push_cast
  ring

lemma spectralGaussian_integrable (t : ℝ) : Integrable (spectralGaussian t) := by
  convert GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (gaussianCoeff_re_pos t) 0 (0 : Plane) using 1
  ext x
  simp [spectralGaussian, neg_mul]

lemma gaussian_damping_integrable :
    Integrable (fun x : Plane => Real.exp (-Real.pi*b*h*‖x‖^2)) := by
  simpa only [spectralGaussian_norm] using (spectralGaussian_integrable 0).norm

lemma spectralGaussian_joint_integrable {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) (ξ : Plane) :
    Integrable (fun q : Plane × ℝ =>
      (Real.fourierChar (-inner ℝ q.1 ξ) : ℂ) * spectralGaussian q.2 q.1 * f q.2)
      (volume.prod μ) := by
  have hc : Continuous (fun q : Plane × ℝ =>
      (Real.fourierChar (-inner ℝ q.1 ξ) : ℂ) * spectralGaussian q.2 q.1) := by
    apply Continuous.mul
    · fun_prop
    · exact spectralGaussian_continuous
  apply (gaussian_damping_integrable.mul_prod hf.norm).mono'
    (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd)
  apply Filter.Eventually.of_forall
  intro q
  change ‖(Real.fourierChar (-inner ℝ q.1 ξ) : ℂ) * spectralGaussian q.2 q.1 * f q.2‖ ≤ _
  rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, spectralGaussian_norm]


lemma spectralGaussian_fourier_integral {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) (ξ : Plane) :
    𝓕 (fun x : Plane => ∫ t, spectralGaussian t x * f t ∂μ) ξ =
      ∫ t, 𝓕 (spectralGaussian t) ξ * f t ∂μ := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  simp_rw [← integral_const_mul]
  have hj : Integrable (Function.uncurry (fun x : Plane => fun t : ℝ =>
      (Real.fourierChar (-inner ℝ x ξ) : ℂ) * (spectralGaussian t x * f t)))
      (volume.prod μ) := by
    convert spectralGaussian_joint_integrable hf ξ using 1
    ext q
    rcases q with ⟨x, t⟩
    change _ * (_ * _) = _ * _ * _
    ring
  rw [integral_integral_swap hj]
  apply integral_congr_ae
  filter_upwards with t
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with x
  ring

end SharpPlanar

namespace SharpPlanar



lemma fourier_integrable {g : Plane → ℂ} (hg : Integrable g) (ξ : Plane) :
    Integrable (fun x : Plane => (Real.fourierChar (-inner ℝ x ξ) : ℂ) * g x) := by
  simpa only [Circle.smul_def, smul_eq_mul] using
    (Real.fourierIntegral_convergent_iff ξ).mpr hg

lemma fourier_conj_even {g : Plane → ℂ} (he : ∀ x, g (-x) = g x) (ξ : Plane) :
    𝓕 (fun x => conj (g x)) ξ = conj (𝓕 g ξ) := by
  simp only [Real.fourier_eq', smul_eq_mul]
  rw [← integral_conj]
  rw [← integral_neg_eq_self (fun x : Plane =>
    conj (Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * g x))]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_neg_left, he, map_mul]
  congr 1
  simp only [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma complex_re_as_sum (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  apply Complex.ext <;> simp

lemma fourier_integrable_exp {g : Plane → ℂ} (hg : Integrable g) (ξ : Plane) :
    Integrable (fun x : Plane =>
      Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * g x) := by
  convert fourier_integrable hg ξ using 1
  funext x
  congr 1
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring


lemma fourier_re_even {g : Plane → ℂ} (hg : Integrable g)
    (he : ∀ x, g (-x) = g x) (ξ : Plane) :
    𝓕 (fun x => ((g x).re : ℂ)) ξ = ((𝓕 g ξ).re : ℂ) := by
  have hgc : Integrable (fun x => conj (g x)) := by
    exact RCLike.conjCLE.toContinuousLinearMap.integrable_comp hg
  calc
    _ = (𝓕 g ξ + 𝓕 (fun x => conj (g x)) ξ) / 2 := by
      simp only [Real.fourier_eq', smul_eq_mul]
      rw [← integral_add (fourier_integrable_exp hg ξ)
        (fourier_integrable_exp hgc ξ), ← integral_div]
      apply integral_congr_ae
      filter_upwards with x
      rw [complex_re_as_sum]
      ring
    _ = _ := by rw [fourier_conj_even he, ← complex_re_as_sum]

end SharpPlanar

namespace SharpPlanar

noncomputable def gaussianSpectral (μ : Measure ℝ) (f : ℝ → ℂ) (x : Plane) : ℂ :=
  ∫ t, spectralGaussian t x * f t ∂μ

lemma gaussianSpectral_integrable {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) : Integrable (gaussianSpectral μ f) := by
  have hi := (spectralGaussian_joint_integrable hf (0 : Plane)).integral_prod_left
  unfold gaussianSpectral
  simpa [Real.fourierChar_apply] using hi

lemma gaussianSpectral_even (μ : Measure ℝ) (f : ℝ → ℂ) (x : Plane) :
    gaussianSpectral μ f (-x) = gaussianSpectral μ f x := by
  simp [gaussianSpectral, spectralGaussian]

lemma gaussianSpectral_eq (μ : Measure ℝ) (f : ℝ → ℂ) (x : Plane) :
    gaussianSpectral μ f x =
      (Real.exp (-Real.pi*h*(b*‖x‖^2)) : ℂ) * spectral μ f (b*‖x‖^2) := by
  rw [gaussianSpectral, spectral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  unfold spectralGaussian gaussianCoeff
  congr 1
  push_cast
  ring

lemma gaussianSpectral_fourier {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) (ξ : Plane) :
    𝓕 (gaussianSpectral μ f) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) *
        ∫ t, kernelMoment 0 (b*‖ξ‖^2) t * f t ∂μ := by
  unfold gaussianSpectral
  rw [spectralGaussian_fourier_integral hf]
  simp_rw [spectralGaussian_fourier, mul_assoc]
  rw [integral_const_mul]

lemma gaussianSpectral_dirac_fourier (t : ℝ) (c : ℂ) (ξ : Plane) :
    𝓕 (gaussianSpectral (Measure.dirac t) (fun _ => c)) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) * kernelMoment 0 (b*‖ξ‖^2) t * c := by
  rw [gaussianSpectral_fourier (integrable_dirac (by finiteness)), integral_dirac]
  ring

lemma density_piece_integrable (p : CardinalData) {j : ℕ} (hj : j < 6) :
    IntegrableOn (density p j) (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply (continuousOn_density p j).mono
  intro t ht
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ hj)
  have hj0 : (0 : ℝ) ≤ j := by positivity
  constructor <;> linarith [ht.1, ht.2]

lemma fourier_add_integrable {f g : Plane → ℂ} (hf : Integrable f)
    (hg : Integrable g) (ξ : Plane) :
    𝓕 (fun x => f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  simp only [Real.fourier_eq', smul_eq_mul, mul_add]
  rw [integral_add (fourier_integrable_exp hf ξ) (fourier_integrable_exp hg ξ)]

lemma fourier_sum_integrable {ι : Type*} (s : Finset ι) (f : ι → Plane → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i)) (ξ : Plane) :
    𝓕 (fun x => ∑ i ∈ s, f i x) ξ = ∑ i ∈ s, 𝓕 (f i) ξ := by
  classical
  simp only [Real.fourier_eq', smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum s (fun i hi => fourier_integrable_exp (hf i hi) ξ)]

noncomputable def qComplex (p : CardinalData) (x : Plane) : ℂ :=
  gaussianSpectral (Measure.dirac 0) (fun _ => (p.C : ℂ)*Pcoeff 0) x +
    (∑ j ∈ Finset.Icc (1 : ℕ) 6,
      gaussianSpectral (Measure.dirac ((j : ℝ)/6))
        (fun _ => 2*(p.C : ℂ)*Pcoeff j) x) +
    (∑ j ∈ Finset.range 6,
      gaussianSpectral (volume.restrict (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)))
        (density p j) x)

lemma qComplex_integrable (p : CardinalData) : Integrable (qComplex p) := by
  apply Integrable.add
  · apply Integrable.add
    · exact gaussianSpectral_integrable (integrable_dirac (by finiteness))
    · exact integrable_finsetSum _ fun j _ =>
        gaussianSpectral_integrable (integrable_dirac (by finiteness))
  · exact integrable_finsetSum _ fun j hj =>
      gaussianSpectral_integrable (density_piece_integrable p (Finset.mem_range.mp hj))

lemma qComplex_even (p : CardinalData) (x : Plane) : qComplex p (-x) = qComplex p x := by
  simp only [qComplex, gaussianSpectral_even]

lemma qComplex_re (p : CardinalData) (x : Plane) : (qComplex p x).re = qSchwartz p x := by
  rw [qSchwartz_apply]
  simp only [qComplex, gaussianSpectral_eq, ← Finset.mul_sum, ← mul_add]
  simp only [cardinal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

lemma qComplex_fourier (p : CardinalData) (ξ : Plane) :
    (𝓕 (qComplex p) ξ).re =
      Real.exp (-Real.pi*h*(b*‖ξ‖^2)) * K p 0 (b*‖ξ‖^2) := by
  have h₀ : Integrable (gaussianSpectral (Measure.dirac 0)
      (fun _ => (p.C : ℂ)*Pcoeff 0)) :=
    gaussianSpectral_integrable (integrable_dirac (by finiteness))
  have h₁ : ∀ j ∈ Finset.Icc (1 : ℕ) 6,
      Integrable (gaussianSpectral (Measure.dirac ((j : ℝ)/6))
        (fun _ => 2*(p.C : ℂ)*Pcoeff j)) := fun _ _ =>
    gaussianSpectral_integrable (integrable_dirac (by finiteness))
  have h₂ : ∀ j ∈ Finset.range 6,
      Integrable (gaussianSpectral (volume.restrict
        (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6))) (density p j)) := fun j hj =>
    gaussianSpectral_integrable (density_piece_integrable p (Finset.mem_range.mp hj))
  unfold qComplex
  have h01 : Integrable (fun x =>
      gaussianSpectral (Measure.dirac 0) (fun _ => (p.C : ℂ)*Pcoeff 0) x +
      ∑ j ∈ Finset.Icc (1 : ℕ) 6, gaussianSpectral (Measure.dirac ((j : ℝ)/6))
        (fun _ => 2*(p.C : ℂ)*Pcoeff j) x) := h₀.add (integrable_finsetSum _ h₁)
  rw [fourier_add_integrable h01
      (integrable_finsetSum _ h₂),
    fourier_add_integrable h₀ (integrable_finsetSum _ h₁),
    fourier_sum_integrable _ _ h₁, fourier_sum_integrable _ _ h₂]
  simp_rw [gaussianSpectral_dirac_fourier]
  have hd : ∀ j ∈ Finset.range 6,
      𝓕 (gaussianSpectral (volume.restrict
        (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6))) (density p j)) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) *
        ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
          density p j t * kernelMoment 0 (b*‖ξ‖^2) t := by
    intro j hj
    rw [gaussianSpectral_fourier (density_piece_integrable p (Finset.mem_range.mp hj)),
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    exact mul_comm _ _
  rw [Finset.sum_congr rfl hd]
  simp only [mul_assoc, ← Finset.mul_sum, ← mul_add]
  have ha : kernelMoment 0 (b*‖ξ‖^2) 0 * ((p.C : ℂ)*Pcoeff 0) +
      (∑ j ∈ Finset.Icc (1 : ℕ) 6,
        kernelMoment 0 (b*‖ξ‖^2) ((j : ℝ)/6) * (2*((p.C : ℂ)*Pcoeff j))) =
      (p.C : ℂ) * (Pcoeff 0 * kernelMoment 0 (b*‖ξ‖^2) 0 +
        ∑ j ∈ Finset.Icc (1 : ℕ) 6,
          2 * Pcoeff j * kernelMoment 0 (b*‖ξ‖^2) ((j : ℝ)/6)) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  rw [ha]
  simp only [K, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma qSchwartz_fourier (p : CardinalData) (ξ : Plane) :
    𝓕 (fun x : Plane => (qSchwartz p x : ℂ)) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) * K p 0 (b*‖ξ‖^2) : ℝ) := by
  simp_rw [← qComplex_re]
  rw [fourier_re_even (qComplex_integrable p) (qComplex_even p), qComplex_fourier]

end SharpPlanar

end OAI
