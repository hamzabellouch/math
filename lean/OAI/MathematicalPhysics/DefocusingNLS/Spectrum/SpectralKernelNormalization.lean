import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNormalizedKernelLimit

namespace OAI

/-! Nearby nonzero kernel vectors admit the fixed functional normalization. -/

namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem spectral_kernel_functional_ne_zero (K₀ K : E →L[ℂ] E)
    (L : E →L[ℂ] ℂ) (c : ℝ) (hc : 0 < c)
    (hbase : ∀ w : E, L w=0 → c * ‖w‖ ≤ ‖w-K₀ w‖)
    (hclose : ‖K-K₀‖ ≤ c/2) (v : E) (hv : K v=v) (hv₀ : v ≠ 0) : L v ≠ 0 := by
  intro hL
  have hb := kernel_complement_perturbation_estimate K₀ K L c hbase hclose v hL
  rw [hv,sub_self,norm_zero] at hb
  have hp := mul_pos (half_pos hc) (norm_pos_iff.mpr hv₀)
  exact (not_le_of_gt hp) hb

theorem spectral_normalize_kernel (K : E →L[ℂ] E) (L : E →L[ℂ] ℂ)
    (v : E) (hv : K v=v) (hL : L v ≠ 0) :
    K ((L v)⁻¹ • v)=(L v)⁻¹ • v ∧ L ((L v)⁻¹ • v)=1 := by
  constructor
  · rw [map_smul,hv]
  · rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hL]

end DefocusingNLS

end OAI
