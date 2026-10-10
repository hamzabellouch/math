import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatLaplacian

namespace OAI

/-! The Gaussian heat equation transferred to bounded smooth initial data. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open Real MeasureTheory Set Filter ShearFlows
open scoped Topology ContDiff BigOperators

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

def spatialPartial (j : Fin 2) (f : Plane → F) (x : Plane) : F :=
  fderiv ℝ f x (Pi.single j 1)

theorem partial_smooth {f : Plane → F} (hf : ContDiff ℝ ∞ f) (j : Fin 2) :
    ContDiff ℝ ∞ (spatialPartial F j f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem slice_one_hasDerivAt {f : Plane → F} (hf : ContDiff ℝ ∞ f) (r s : ℝ) :
    HasDerivAt (fun y => f ![r,y]) (spatialPartial F 1 f ![r,s]) s := by
  have hi : HasDerivAt (fun y : ℝ => (![r,y] : Plane)) (Pi.single 1 1) s := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · change HasDerivAt (fun _ : ℝ => r) (0 : ℝ) s
      exact hasDerivAt_const s r
    · change HasDerivAt (fun y : ℝ => y) (1 : ℝ) s
      convert! hasDerivAt_id s
  exact (hf.differentiable (by simp) ![r,s]).hasFDerivAt.comp_hasDerivAt s hi

theorem slice_zero_hasDerivAt {f : Plane → F} (hf : ContDiff ℝ ∞ f) (r s : ℝ) :
    HasDerivAt (fun y => f ![y,s]) (spatialPartial F 0 f ![r,s]) r := by
  have hi : HasDerivAt (fun y : ℝ => (![y,s] : Plane)) (Pi.single 0 1) r := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · change HasDerivAt (fun y : ℝ => y) (1 : ℝ) r
      convert! hasDerivAt_id r
    · change HasDerivAt (fun _ : ℝ => s) (0 : ℝ) r
      exact hasDerivAt_const r s
  exact (hf.differentiable (by simp) ![r,s]).hasFDerivAt.comp_hasDerivAt r hi

theorem kernelSecond_zero (t : ℝ) (x : Plane) :
    kernelSecond t 0 x = oneDimSecond t (x 0) * oneDim t (x 1) := by
  dsimp [kernelSecond, oneDimSecond, kernel]
  ring

theorem kernelSecond_one (t : ℝ) (x : Plane) :
    kernelSecond t 1 x = oneDim t (x 0) * oneDimSecond t (x 1) := by
  dsimp [kernelSecond, oneDimSecond, kernel]
  ring

/-- A Gaussian second derivative can be moved onto the bounded data. -/
theorem kernelSecond_transfer {t : ℝ} (ht : 0 < t) {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (j : Fin 2) (C D E : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖spatialPartial F j f x‖ ≤ D)
    (hE : ∀ x, ‖spatialPartial F j (spatialPartial F j f) x‖ ≤ E) :
    (∫ x, kernelSecond t j x • f x) =
      ∫ x, kernel t x • spatialPartial F j (spatialPartial F j f) x := by
  fin_cases j
  · change (∫ x, kernelSecond t 0 x • f x) = _
    simp_rw [kernelSecond_zero]
    exact integral_second_zero F ht hf.continuous
      (partial_smooth F (partial_smooth F hf 0) 0).continuous
      (slice_zero_hasDerivAt F hf) (slice_zero_hasDerivAt F (partial_smooth F hf 0))
      C D E hC hD hE
  · change (∫ x, kernelSecond t 1 x • f x) = _
    simp_rw [kernelSecond_one]
    exact integral_second_one F ht hf.continuous
      (partial_smooth F (partial_smooth F hf 1) 1).continuous
      (slice_one_hasDerivAt F hf) (slice_one_hasDerivAt F (partial_smooth F hf 1))
      C D E hC hD hE

theorem partial_reflection {f : Plane → F} (hf : ContDiff ℝ ∞ f)
    (j : Fin 2) (x y : Plane) :
    spatialPartial F j (fun z => f (x-z)) y = -(spatialPartial F j f (x-y)) := by
  have hd := (hf.differentiable (by simp) (x-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id y))
  change HasFDerivAt (fun z => f (x-z)) _ y at hd
  unfold spatialPartial
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

theorem partial_reflection_twice {f : Plane → F} (hf : ContDiff ℝ ∞ f)
    (j : Fin 2) (x y : Plane) :
    spatialPartial F j (spatialPartial F j (fun z => f (x-z))) y =
      spatialPartial F j (spatialPartial F j f) (x-y) := by
  have he : spatialPartial F j (fun z => f (x-z)) = -(fun z => spatialPartial F j f (x-z)) := by
    funext z
    exact partial_reflection F hf j x z
  rw [he]
  change fderiv ℝ (-(fun z => spatialPartial F j f (x-z))) y (Pi.single j 1) = _
  rw [fderiv_neg]
  change -(spatialPartial F j (fun z => spatialPartial F j f (x-z)) y) = _
  rw [partial_reflection F (partial_smooth F hf j), neg_neg]

theorem kernelSecond_convolve {t : ℝ} (ht : 0 < t) {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (j : Fin 2) (C D E : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖spatialPartial F j f x‖ ≤ D)
    (hE : ∀ x, ‖spatialPartial F j (spatialPartial F j f) x‖ ≤ E) (x : Plane) :
    BoundedKernel.convolve Plane F volume (kernelSecond t j) f x =
      BoundedKernel.convolve Plane F volume (kernel t) (spatialPartial F j (spatialPartial F j f)) x := by
  have hg : ContDiff ℝ ∞ (fun y => f (x-y)) := hf.comp (contDiff_const.sub contDiff_id)
  have h := kernelSecond_transfer F ht hg j C D E
    (fun y => hC (x-y))
    (fun y => by simpa only [partial_reflection F hf, norm_neg] using hD (x-y))
    (fun y => by simpa only [partial_reflection_twice F hf] using hE (x-y))
  change (∫ y, kernelSecond t j y • f (x-y)) =
    ∫ y, kernel t y • spatialPartial F j (spatialPartial F j f) (x-y)
  simpa only [partial_reflection_twice F hf] using h

/-- The time derivative is the sum of heat evolutions of the actual second partials. -/
theorem hasDerivAt_heatConvolution_data {t : ℝ} (ht : 0 < t) {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (C D E : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ j x, ‖spatialPartial F j f x‖ ≤ D)
    (hE : ∀ j x, ‖spatialPartial F j (spatialPartial F j f) x‖ ≤ E) (x : Plane) :
    HasDerivAt (fun s => heatConvolution F s f x)
      (∑ j : Fin 2, heatConvolution F t (spatialPartial F j (spatialPartial F j f)) x) t := by
  have hd := hasDerivAt_heatConvolution F ht f hf.continuous C hC x
  convert! hd using 1
  rw [← integral_sub_left_eq_self _ volume x]
  simp only [sub_sub_self]
  simp_rw [Finset.sum_smul]
  rw [integral_finsetSum _ (fun j _ =>
    BoundedKernel.integrand_integrable Plane F volume (kernelSecond t j) f
      (kernelSecond_integrable ht j) hf.continuous C hC x)]
  apply Finset.sum_congr rfl
  intro j _
  rw [heatConvolution_eq]
  exact (kernelSecond_convolve F ht hf j C D E hC (hD j) (hE j) x).symm

theorem norm_partial_le {f : Plane → F} (j : Fin 2) (D : ℝ)
    (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (x : Plane) : ‖spatialPartial F j f x‖ ≤ D := by
  have h := (fderiv ℝ f x).le_opNorm (Pi.single j 1)
  simpa only [spatialPartial, Pi.norm_single, norm_one, mul_one] using h.trans
    (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _))

theorem partial_heatConvolution {t : ℝ} (ht : 0 < t) {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (j : Fin 2) (C D : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (x : Plane) :
    spatialPartial F j (heatConvolution F t f) x = heatConvolution F t (spatialPartial F j f) x := by
  have he : heatConvolution F t f =
      BoundedKernel.convolve Plane F volume (kernel t) f :=
    funext (heatConvolution_eq F t f)
  have hi := BoundedKernel.integrand_integrable Plane (Plane →L[ℝ] F) volume (kernel t)
    (fderiv ℝ f) (kernel_integrable ht) (hf.continuous_fderiv (by simp)) D hD x
  rw [spatialPartial, he, BoundedKernel.fderiv_convolve Plane F volume (kernel t) f
    (kernel_integrable ht) (hf.of_le (by simp)) C D hC hD x,
    ContinuousLinearMap.integral_apply hi, heatConvolution_eq]
  rfl

theorem gradient_convolve_data {t : ℝ} (ht : 0 < t) {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (j : Fin 2) (C D : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (x : Plane) :
    BoundedKernel.convolve Plane F volume (kernelDerivative t j) f x =
      heatConvolution F t (spatialPartial F j f) x := by
  rw [← fderiv_heatConvolution_basis F ht f hf.continuous C hC x j]
  exact partial_heatConvolution F ht hf j C D hC hD x

/-- The actual heat convolution solves the heat equation, with no assumed PDE input. -/
theorem hasDerivAt_heatConvolution_equation {t : ℝ} (ht : 0 < t) {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (C D E : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D)
    (hE : ∀ j x, ‖fderiv ℝ (spatialPartial F j f) x‖ ≤ E) (x : Plane) :
    HasDerivAt (fun s => heatConvolution F s f x)
      (∑ j : Fin 2, spatialPartial F j (spatialPartial F j (heatConvolution F t f)) x) t := by
  convert! hasDerivAt_heatConvolution_data F ht hf C D E hC
    (fun j => norm_partial_le F j D hD) (fun j => norm_partial_le F j E (hE j)) x using 1
  apply Finset.sum_congr rfl
  intro j _
  have he : spatialPartial F j (heatConvolution F t f) =
      heatConvolution F t (spatialPartial F j f) :=
    funext (partial_heatConvolution F ht hf j C D hC hD)
  rw [he, partial_heatConvolution F ht (partial_smooth F hf j) j D E
    (norm_partial_le F j D hD) (hE j)]

end ForcedComputation.PlaneHeat

end

end OAI
