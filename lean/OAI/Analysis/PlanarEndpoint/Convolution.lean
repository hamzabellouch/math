import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphTree
import OAI.Analysis.PlanarEndpoint.Heat

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped Topology
namespace PlanarEndpoint

def heatFrequency (a : ℝ) (x η : Plane) : ℂ :=
  Complex.exp (-((4*a*Real.pi^2 : ℝ) : ℂ) * (‖η‖ : ℂ)^2 +
    2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ (-x) η : ℝ) : ℂ))

lemma norm_heatFrequency (a : ℝ) (x η : Plane) :
    ‖heatFrequency a x η‖ = gaussianWeight (4*a*Real.pi^2) η := by
  simp only [heatFrequency, Complex.norm_exp, ← Complex.ofReal_pow, Complex.add_re, Complex.mul_re,
    Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, Complex.mul_im, zero_add, add_zero]
  simp [gaussianWeight]

lemma integrable_heatFrequency {a : ℝ} (ha : 0 < a) (x : Plane) :
    Integrable (heatFrequency a x) volume := by
  exact (integrable_gaussianWeight (by positivity : 0 < 4*a*Real.pi^2)).mono'
    (by unfold heatFrequency; fun_prop) (Eventually.of_forall fun η => (norm_heatFrequency _ _ _).le)

lemma memLp_heatFrequency {a : ℝ} (ha : 0 < a) (x : Plane) :
    MemLp (heatFrequency a x) 2 volume := by
  apply (memLp_gaussian (show 0 < 4*a*Real.pi^2 by positivity)).mono
    (by unfold heatFrequency; fun_prop)
  filter_upwards [] with η
  rw [norm_heatFrequency]
  simp only [Complex.norm_exp, ← Complex.ofReal_neg, Complex.ofReal_re]
  simp [gaussianWeight]

lemma inverse_heatFrequency {a : ℝ} (ha : 0 < a) (x y : Plane) :
    (𝓕⁻ (heatFrequency a x)) y = (heatKernel a (x-y) : ℂ) := by
  rw [Real.fourierInv_eq_fourier_neg]
  unfold heatFrequency
  rw [fourier_gaussian_innerProductSpace' (by simpa only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.ofReal_ofNat] using (show 0 < 4*a*Real.pi^2 by positivity))]
  have hd : (Module.finrank ℝ Plane : ℂ) / 2 = 1 := by
    simp [Plane, finrank_euclideanSpace]
  rw [hd, Complex.cpow_one]
  have hn : ‖-x - -y‖ = ‖x-y‖ := by rw [neg_sub_neg, norm_sub_rev]
  rw [hn]
  simp only [heatKernel, gaussianWeight, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat]
  congr 1
  · field_simp [ha.ne', Real.pi_ne_zero]

  · congr 1
    field_simp [ha.ne', Real.pi_ne_zero]

lemma inverse_heatFrequency_l2_ae {a : ℝ} (ha : 0 < a) (x : Plane) :
    ((Lp.fourierTransformₗᵢ Plane ℂ).symm
      ((memLp_heatFrequency ha x).toLp (heatFrequency a x)) : Plane → ℂ) =ᵐ[volume]
      fun y => (heatKernel a (x-y) : ℂ) := by
  have hto := (memLp_heatFrequency ha x).coeFn_toLp
  have hi : Integrable ((memLp_heatFrequency ha x).toLp (heatFrequency a x) : Plane → ℂ)
      volume := (integrable_heatFrequency ha x).congr hto.symm
  have hh := l2_inverse_fourier_ae ((memLp_heatFrequency ha x).toLp (heatFrequency a x)) hi
  filter_upwards [hh] with y hy
  rw [hy]
  have he : (𝓕⁻ ((memLp_heatFrequency ha x).toLp (heatFrequency a x) : Plane → ℂ)) y =
      (𝓕⁻ (heatFrequency a x)) y := by
    rw [Real.fourierInv_eq', Real.fourierInv_eq']
    exact integral_congr_ae (hto.mono fun η hη => by dsimp only; rw [hη])
  rw [he, inverse_heatFrequency ha]

lemma conjugate_heatFrequency (a : ℝ) (x η : Plane) :
    starRingEnd ℂ (heatFrequency a x η) =
      phase x 0 ((2 * Real.pi) • η) *
        (gaussianWeight a ((2 * Real.pi) • η) : ℂ) := by
  unfold heatFrequency phase gaussianWeight
  rw [← Complex.exp_conj, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [map_add, map_mul, map_neg, map_pow, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, inner_neg_left, inner_smul_right, zero_mul, sub_zero,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  push_cast
  ring

lemma abel_eq_frequency_pairing (f : L2) (a : ℝ) (x : Plane) (t : ℝ) :
    abel f a x t = ∫ η : Plane,
      (evolutionMultiplier t η * (Lp.fourierTransformₗᵢ Plane ℂ f) η) *
        starRingEnd ℂ (heatFrequency a x η) := by
  let q : Plane → ℂ := fun η =>
    (evolutionMultiplier t η * (Lp.fourierTransformₗᵢ Plane ℂ f) η) *
      starRingEnd ℂ (heatFrequency a x η)
  have he : ∫ ξ : Plane, phase x t ξ * (gaussianWeight a ξ : ℂ) * fourier f ξ =
      ∫ ξ : Plane, q ((2 * Real.pi)⁻¹ • ξ) := by
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp only [q]
    rw [conjugate_heatFrequency]
    simp only [evolutionMultiplier, smul_smul, mul_inv_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_smul]
    change phase x t ξ * (gaussianWeight a ξ : ℂ) * fourier f ξ =
      (phase 0 t ξ * fourier f ξ) * (phase x 0 ξ * (gaussianWeight a ξ : ℂ))
    have hp : phase x t ξ = phase x 0 ξ * phase 0 t ξ := by
      simp only [phase, inner_zero_left, zero_mul, sub_zero, zero_sub, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  rw [abel_eq_weighted, he, Measure.integral_comp_inv_smul_of_nonneg volume q
    (by positivity : 0 ≤ 2 * Real.pi)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul,
    inv_mul_cancel₀ (by positivity : (2 * Real.pi)^2 ≠ 0), one_smul]
  rfl

lemma abel_eq_heat_convolution (f : L2) {a : ℝ} (ha : 0 < a) (x : Plane) (t : ℝ) :
    abel f a x t = ∫ y : Plane, (heatKernel a (x-y) : ℂ) * l2Evolution f t y := by
  let k : L2 := (memLp_heatFrequency ha x).toLp (heatFrequency a x)
  let F := Lp.fourierTransformₗᵢ Plane ℂ
  have hk : (k : Plane → ℂ) =ᵐ[volume] heatFrequency a x :=
    (memLp_heatFrequency ha x).coeFn_toLp
  have hki := inverse_heatFrequency_l2_ae ha x
  calc
    abel f a x t = inner ℂ k (F (l2Evolution f t)) := by
      rw [abel_eq_frequency_pairing, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hk, l2Evolution_fourier_ae f t] with η hη hFη
      rw [RCLike.inner_apply, hη, hFη]
    _ = inner ℂ (F.symm k) (l2Evolution f t) := by
      simpa using (F.symm.inner_map_map k (F (l2Evolution f t))).symm
    _ = ∫ y : Plane, (heatKernel a (x-y) : ℂ) * l2Evolution f t y := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hki] with y hy
      rw [RCLike.inner_apply, hy, Complex.conj_ofReal, mul_comm]

lemma integrable_heat_convolution (f : L2) {a : ℝ} (ha : 0 < a)
    (x : Plane) (t : ℝ) :
    Integrable (fun y : Plane => (heatKernel a (x-y) : ℂ) * l2Evolution f t y) volume := by
  let k : L2 := (memLp_heatFrequency ha x).toLp (heatFrequency a x)
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
    ((Lp.fourierTransformₗᵢ Plane ℂ).symm k) (l2Evolution f t)
  apply hi.congr
  filter_upwards [inverse_heatFrequency_l2_ae ha x] with y hy
  rw [RCLike.inner_apply, hy, Complex.conj_ofReal, mul_comm]

end PlanarEndpoint
end

end OAI
