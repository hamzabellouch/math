import OAI.Geometry.Perimeter.Regularity.EllipticCurl

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem compactSupport_bounded_derivative {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : V → W} (hf : Continuous (fderiv ℝ f)) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖fderiv ℝ f x‖≤C := by
  obtain ⟨C,hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hf
  exact ⟨C,(norm_nonneg _).trans (hC 0),hC⟩

theorem compact_kernel_bounded_second {k : Euc n → ℝ}
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ k) x‖≤C := by
  have hk' : ContDiff ℝ ∞ (fderiv ℝ k) := hk.fderiv_right (by simp)
  exact compactSupport_bounded_derivative (hk'.continuous_fderiv (by simp)) (hc.fderiv ℝ)

theorem kernel_derivative_lipschitz {k : Euc n → ℝ}
    (hk : ContDiff ℝ ∞ k) {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ (fderiv ℝ k) x‖≤C) (x z : Euc n) :
    ‖fderiv ℝ k z-fderiv ℝ k x‖≤C*‖z-x‖ := by
  have hk' : ContDiff ℝ ∞ (fderiv ℝ k) := hk.fderiv_right (by simp)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ k)
    (fun z _ ↦ hk'.differentiable (by simp) z) (fun z _ ↦ hC z)
    convex_univ (mem_univ x) (mem_univ z)

theorem kernel_taylor_of_derivative_lipschitz {k : Euc n → ℝ}
    (hk : Differentiable ℝ k) {C : ℝ} (hC0 : 0≤C)
    (hLip : ∀ x z, ‖fderiv ℝ k z-fderiv ℝ k x‖≤C*‖z-x‖)
    (x y : Euc n) : ‖k (x+y)-k x-fderiv ℝ k x y‖≤C*‖y‖^2 := by
  have hb : ∀ z ∈ Metric.closedBall x ‖y‖, ‖fderiv ℝ k z-fderiv ℝ k x‖≤C*‖y‖ := by
    intro z hz
    exact (hLip x z).trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) hC0)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := k)
    (fun z (_ : z∈Metric.closedBall x ‖y‖) ↦ hk z) hb
    (convex_closedBall x ‖y‖) (Metric.mem_closedBall_self (norm_nonneg y))
    (show x+y ∈ Metric.closedBall x ‖y‖ by simp [Metric.mem_closedBall,dist_eq_norm])
  simpa only [add_sub_cancel_left,pow_two,mul_assoc] using h

theorem compact_kernel_uniform_taylor {k : Euc n → ℝ}
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y : Euc n,
      ‖k (x+y)-k x-fderiv ℝ k x y‖≤C*‖y‖^2 := by
  obtain ⟨C,hC0,hC⟩ := compact_kernel_bounded_second hk hc
  exact ⟨C,hC0,kernel_taylor_of_derivative_lipschitz (hk.differentiable (by simp)) hC0
    (kernel_derivative_lipschitz hk hC)⟩

def kernelLinear (u k : Euc n → ℝ) : Euc n →L[ℝ] ℝ :=
  ∫ x, u x • fderiv ℝ k (-x)

theorem kernelLinear_integrable {u k : Euc n → ℝ} (hu : Integrable u volume)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    Integrable (fun x ↦ u x • fderiv ℝ k (-x)) volume := by
  obtain ⟨M,hM⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hk.continuous_fderiv (by simp))
  apply (hu.norm.mul_const M).mono'
    (hu.aestronglyMeasurable.smul (((hk.continuous_fderiv (by simp)).comp continuous_neg).aestronglyMeasurable))
  exact ae_of_all _ fun x ↦ by change ‖u x • fderiv ℝ k (-x)‖ ≤ ‖u x‖*M; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hM (-x)) (norm_nonneg _)

theorem kernelLinear_apply {u k : Euc n → ℝ} (hu : Integrable u volume)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (y : Euc n) :
    kernelLinear u k y = ∫ x, u x*fderiv ℝ k (-x) y := by
  exact ContinuousLinearMap.integral_apply (kernelLinear_integrable hu hk hc) y

theorem convolution_uniform_taylor {k : Euc n → ℝ}
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ∃ C : ℝ, 0≤C ∧ ∀ u : Euc n → ℝ, Integrable u volume → ∀ y : Euc n,
      ‖(k ⋆[lsmul ℝ ℝ,volume] u) y-(k ⋆[lsmul ℝ ℝ,volume] u) 0-kernelLinear u k y‖ ≤
        C*(∫ x, ‖u x‖)*‖y‖^2 := by
  obtain ⟨C,hC,hTaylor⟩ := compact_kernel_uniform_taylor hk hc
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hk.continuous
  refine ⟨C,hC,fun u hu y ↦ ?_⟩
  have hi (z : Euc n) : Integrable (fun x ↦ u x*k (z-x)) volume :=
    hu.mul_bdd ((hk.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun x ↦ hM (z-x))
  have hil : Integrable (fun x ↦ u x*fderiv ℝ k (-x) y) volume :=
    ((ContinuousLinearMap.apply ℝ ℝ y).integrable_comp (kernelLinear_integrable hu hk hc))
  rw [convolution_eq_swap,convolution_eq_swap,kernelLinear_apply hu hk hc]
  change ‖(∫ x, k (y-x)*u x)-(∫ x, k (0-x)*u x)-(∫ x, u x*fderiv ℝ k (-x) y)‖ ≤ _
  simp_rw [mul_comm (k _)]
  have his : Integrable (fun x ↦ u x*k (y-x)-u x*k (0-x)) volume := (hi y).sub (hi 0)
  rw [← integral_sub (hi y) (hi 0),← integral_sub his hil]
  have he : (fun x ↦ u x*k (y-x)-u x*k (0-x)-u x*fderiv ℝ k (-x) y) =
      fun x ↦ (k ((-x)+y)-k (-x)-fderiv ℝ k (-x) y)*u x := by
    funext x
    rw [zero_sub,show y-x=(-x)+y by abel]
    ring
  rw [he]
  have hb : ∀ᵐ x ∂volume,
      ‖(k ((-x)+y)-k (-x)-fderiv ℝ k (-x) y)*u x‖≤(C*‖y‖^2)*‖u x‖ :=
    ae_of_all _ fun x ↦ by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hTaylor (-x) y) (norm_nonneg _)
  have h := norm_integral_le_of_norm_le (hu.norm.const_mul (C*‖y‖^2)) hb
  rw [integral_const_mul] at h
  convert h using 1
  ring

end RPISingularHarnack

end

end OAI
