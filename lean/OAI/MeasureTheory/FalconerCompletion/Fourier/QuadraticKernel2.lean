import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def quadraticKernelND (a : ℂ) (ξ : V) : ℂ :=
  ((Real.pi:ℂ)/a)^(Module.finrank ℝ V/2:ℂ) *
    Complex.exp (-(Real.pi:ℂ)^2*(‖ξ‖:ℂ)^2/a)

lemma fourier_quadraticGaussianND {a : ℂ} (ha : 0 < a.re) (ξ : V) :
    𝓕 (fun x : V => Complex.exp (-a*(‖x‖:ℂ)^2)) ξ = quadraticKernelND a ξ := by
  exact fourier_gaussian_innerProductSpace ha ξ

lemma quadraticGaussianND_pairing {a : ℂ} (ha : 0 < a.re) (φ : 𝓢(V,ℂ)) :
    (∫ x : V, Complex.exp (-a*(‖x‖:ℂ)^2) * 𝓕 φ x) =
      ∫ ξ : V, quadraticKernelND a ξ * φ ξ := by
  have hi : Integrable (fun x : V => Complex.exp (-a*(‖x‖:ℂ)^2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add ha 0 (0:V)
  have hh := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
    (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner hi φ.integrable
  have hflip : (innerₗ V : V →ₗ[ℝ] V →ₗ[ℝ] ℝ).flip = innerₗ V := by
    ext x y
    exact real_inner_comm x y
  rw [hflip] at hh
  have he : (∫ x : V, Complex.exp (-a*(‖x‖:ℂ)^2) * 𝓕 φ x) =
      ∫ ξ : V, 𝓕 (fun x : V => Complex.exp (-a*(‖x‖:ℂ)^2)) ξ * φ ξ := by
    simpa only [smul_eq_mul] using! hh.symm
  rw [he]
  simp only [fourier_quadraticGaussianND ha]

lemma quadratic_exponentialND_norm_le_one {a : ℂ} (ha : 0 ≤ a.re) (r : ℝ) :
    ‖Complex.exp (-(Real.pi:ℂ)^2*(r:ℂ)^2/a)‖ ≤ 1 := by
  have he : -(Real.pi:ℂ)^2*(r:ℂ)^2/a = ((-Real.pi^2*r^2:ℝ):ℂ)*a⁻¹ := by
    push_cast
    ring
  rw [he,Complex.norm_exp,Complex.re_ofReal_mul]
  apply Real.exp_le_one_iff.mpr
  have hi : 0 ≤ a⁻¹.re := by rw [Complex.inv_re]; exact div_nonneg ha (Complex.normSq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg Real.pi)) (sq_nonneg r)) hi

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma quadraticKernelND_norm_le {a : ℂ} (ha : 0 ≤ a.re)
    {b : ℝ} (hb : 0 < b) (hn : b ≤ ‖a‖) (ξ : V) :
    ‖quadraticKernelND a ξ‖ ≤ (Real.pi/b)^(Module.finrank ℝ V/2:ℝ) := by
  unfold quadraticKernelND
  rw [norm_mul]
  have hpow : ‖((Real.pi:ℂ)/a)^(Module.finrank ℝ V/2:ℂ)‖ =
      (Real.pi/‖a‖)^(Module.finrank ℝ V/2:ℝ) := by
    convert Complex.norm_cpow_real ((Real.pi:ℂ)/a) (Module.finrank ℝ V/2:ℝ) using 1 <;>
      simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  rw [hpow]
  calc
    _ ≤ (Real.pi/‖a‖)^(Module.finrank ℝ V/2:ℝ)*1 :=
      mul_le_mul_of_nonneg_left (quadratic_exponentialND_norm_le_one ha _) (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left Real.pi_pos.le hb hn) (by positivity)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma quadraticKernelND_damped_bound {b : ℝ} (hb : 0 < b) {ε : ℝ}
    (hε : 0 ≤ ε) (ξ : V) :
    ‖quadraticKernelND ((ε:ℂ)+(b:ℂ)*Complex.I) ξ‖ ≤
      (Real.pi/b)^(Module.finrank ℝ V/2:ℝ) := by
  apply quadraticKernelND_norm_le (by simpa using hε) hb
  have hh := Complex.abs_im_le_norm ((ε:ℂ)+(b:ℂ)*Complex.I)
  simpa [abs_of_pos hb] using hh

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma quadraticKernelND_continuous_damping {b : ℝ} (hb : 0 < b) (ξ : V) :
    ContinuousAt (fun ε : ℝ => quadraticKernelND ((ε:ℂ)+(b:ℂ)*Complex.I) ξ) 0 := by
  have hn : (b:ℂ)*Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne') Complex.I_ne_zero
  unfold quadraticKernelND
  apply ContinuousAt.mul
  · have ht : ContinuousAt (fun ε : ℝ => (Real.pi:ℂ)/((ε:ℂ)+(b:ℂ)*Complex.I)) 0 :=
      continuousAt_const.div (by fun_prop) (by simpa using hn)
    by_cases hdim : Module.finrank ℝ V=0
    · simpa only [hdim,Nat.cast_zero,zero_div,Complex.cpow_zero] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (1:ℂ)) 0)
    · have hp : ContinuousAt (fun z : ℂ => z^(Module.finrank ℝ V/2:ℂ))
          ((Real.pi:ℂ)/((0:ℂ)+(b:ℂ)*Complex.I)) :=
        Complex.continuousAt_cpow_const_of_re_pos
          (Or.inl (show 0 ≤ ((Real.pi:ℂ)/((0:ℂ)+(b:ℂ)*Complex.I)).re by simp [Complex.div_re]))
          (show 0 < (Module.finrank ℝ V/2:ℂ).re by
            simp only [Complex.div_ofNat_re,Complex.natCast_re]
            positivity)
      exact hp.comp (f := fun ε : ℝ => (Real.pi:ℂ)/((ε:ℂ)+(b:ℂ)*Complex.I)) (x := 0) ht
  · apply Complex.continuous_exp.continuousAt.comp
    exact continuousAt_const.div (by fun_prop) (by simpa using hn)

lemma quadraticKernelND_integral_limit {b : ℝ} (hb : 0 < b) (φ : 𝓢(V,ℂ)) :
    Tendsto (fun c : ℝ => ∫ ξ : V,
      quadraticKernelND (((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I) ξ * φ ξ) atTop
      (𝓝 (∫ ξ : V, quadraticKernelND ((b:ℂ)*Complex.I) ξ * φ ξ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ξ => (Real.pi/b)^(Module.finrank ℝ V/2:ℝ)*‖φ ξ‖) _ _ (φ.integrable.norm.const_mul _) _
  · filter_upwards with c
    exact (show Continuous (fun ξ : V =>
      quadraticKernelND (((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I) ξ * φ ξ) by
        unfold quadraticKernelND; fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0:ℝ)] with c hc
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (quadraticKernelND_damped_bound hb (inv_nonneg.mpr hc) ξ) (norm_nonneg _)
  · filter_upwards with ξ
    have hh := (quadraticKernelND_continuous_damping hb ξ).tendsto.comp tendsto_inv_atTop_zero
    simpa using hh.mul_const (φ ξ)

lemma quadraticGaussianND_integral_limit {b : ℝ} (φ : 𝓢(V,ℂ)) :
    Tendsto (fun c : ℝ => ∫ x : V,
      Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(‖x‖:ℂ)^2) * 𝓕 φ x) atTop
      (𝓝 (∫ x : V, Complex.exp (-((b:ℂ)*Complex.I)*(‖x‖:ℂ)^2) * 𝓕 φ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖𝓕 φ x‖) _ _ (𝓕 φ).integrable.norm _
  · filter_upwards with c
    exact (show Continuous (fun x : V =>
      Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(‖x‖:ℂ)^2) * 𝓕 φ x) by fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0:ℝ)] with c hc
    filter_upwards with x
    rw [norm_mul]
    have hh : ‖Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(‖x‖:ℂ)^2)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,← Complex.ofReal_pow]
      simp only [mul_zero,add_zero,zero_add,sub_zero,mul_one]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr hc)) (sq_nonneg ‖x‖)
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards with x
    have hh := ((tendsto_inv_atTop_zero.ofReal.add_const ((b:ℂ)*Complex.I)).neg.mul_const ((‖x‖:ℂ)^2)).cexp
    simpa using hh.mul_const (𝓕 φ x)

lemma quadratic_oscillatoryND_pairing {b : ℝ} (hb : 0 < b) (φ : 𝓢(V,ℂ)) :
    (∫ x : V, Complex.exp (-((b:ℂ)*Complex.I)*(‖x‖:ℂ)^2) * 𝓕 φ x) =
      ∫ ξ : V, quadraticKernelND ((b:ℂ)*Complex.I) ξ * φ ξ := by
  have he : (fun c : ℝ => ∫ x : V,
      Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(‖x‖:ℂ)^2) * 𝓕 φ x) =ᶠ[atTop]
      (fun c : ℝ => ∫ ξ : V,
      quadraticKernelND (((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I) ξ * φ ξ) := by
    filter_upwards [Ioi_mem_atTop (0:ℝ)] with c hc
    exact quadraticGaussianND_pairing (a := ((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)
      (by simpa using inv_pos.mpr (show 0 < c from hc)) φ
  exact tendsto_nhds_unique (quadraticGaussianND_integral_limit φ)
    ((quadraticKernelND_integral_limit hb φ).congr' he.symm)

noncomputable def fresnelCoefficientND (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (b : ℝ) : ℂ :=
  (((Real.pi/b)^(Module.finrank ℝ V/2:ℝ):ℝ):ℂ) *
    Complex.exp (-(Real.pi:ℂ)*Module.finrank ℝ V/4*Complex.I)

omit [MeasurableSpace V] [BorelSpace V] in
lemma quadraticND_fresnel_coefficient {b : ℝ} (hb : 0 < b) :
    ((Real.pi:ℂ)/((b:ℂ)*Complex.I))^(Module.finrank ℝ V/2:ℂ) = fresnelCoefficientND V b := by
  have hr : 0 < Real.pi/b := div_pos Real.pi_pos hb
  have hi : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have he : (Real.pi:ℂ)/((b:ℂ)*Complex.I) = ((Real.pi/b:ℝ):ℂ)*(-Complex.I) := by
    push_cast
    field_simp
    simp [Complex.I_sq,div_eq_mul_inv]
  rw [he,Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hi),
    Complex.log_ofReal_mul hr hi,Complex.log_neg_I]
  have hex : (((Real.log (Real.pi/b):ℝ):ℂ)+(-((Real.pi:ℂ)/2)*Complex.I))*(Module.finrank ℝ V/2:ℂ) =
      ((Real.log (Real.pi/b):ℝ):ℂ)*(Module.finrank ℝ V/2:ℂ) +
        (-(Real.pi:ℂ)*Module.finrank ℝ V/4*Complex.I) := by ring
  rw [hex,Complex.exp_add]
  unfold fresnelCoefficientND
  congr 1
  rw [Real.rpow_def_of_pos hr]
  push_cast
  rfl

omit [MeasurableSpace V] [BorelSpace V] in
lemma fresnelCoefficientND_norm {b : ℝ} (hb : 0 < b) :
    ‖fresnelCoefficientND V b‖ = (Real.pi/b)^(Module.finrank ℝ V/2:ℝ) := by
  simp [fresnelCoefficientND,Complex.norm_exp,Complex.mul_re,
    Complex.norm_real,abs_of_nonneg (Real.rpow_nonneg (div_pos Real.pi_pos hb).le _)]

theorem quadratic_stationaryND_identity {b : ℝ} (hb : 0 < b) (φ : 𝓢(V,ℂ)) :
    (∫ x : V, Complex.exp (-((b:ℂ)*Complex.I)*(‖x‖:ℂ)^2)*φ x) =
      fresnelCoefficientND V b *
        ∫ ξ : V, Complex.exp (Complex.I*((Real.pi^2/b*‖ξ‖^2:ℝ):ℂ))*𝓕⁻ φ ξ := by
  have hh := quadratic_oscillatoryND_pairing hb (𝓕⁻ φ)
  simp only [FourierTransform.fourier_fourierInv_eq] at hh
  rw [hh]
  unfold quadraticKernelND
  rw [quadraticND_fresnel_coefficient hb,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  have hex : -(Real.pi:ℂ)^2*(‖ξ‖:ℂ)^2/((b:ℂ)*Complex.I) =
      Complex.I*((Real.pi^2/b*‖ξ‖^2:ℝ):ℂ) := by
    push_cast
    field_simp
    simp only [Complex.I_sq]
    ring
  rw [hex]
  exact mul_assoc _ _ _

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
