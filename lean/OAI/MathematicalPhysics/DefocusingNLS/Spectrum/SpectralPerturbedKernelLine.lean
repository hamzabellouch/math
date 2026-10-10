import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralKernelNormalization

namespace OAI

/-! The fixed-complement estimate preserves a one-dimensional kernel. -/

namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem spectral_kernel_line_of_close (K₀ K : E →L[ℂ] E)
    (L : E →L[ℂ] ℂ) (c : ℝ) (hc : 0 < c)
    (hbase : ∀ w : E, L w=0 → c * ‖w‖ ≤ ‖w-K₀ w‖)
    (hclose : ‖K-K₀‖ ≤ c/2) (u v : E) (hu : K u=u) (hne : u ≠ 0) (hv : K v=v) :
    ∃ a : ℂ, v=a • u := by
  have hLu := spectral_kernel_functional_ne_zero K₀ K L c hc hbase hclose u hu hne
  let a : ℂ := L v / L u
  have hnorm : L (a • u)=L v := by
    rw [map_smul,smul_eq_mul]
    exact div_mul_cancel₀ (L v) hLu
  have hfix : K (a • u)=a • u := by rw [map_smul,hu]
  refine ⟨a,?_⟩
  exact (kernel_unique_with_normalization K L (c/2) (half_pos hc)
    (fun w hw => kernel_complement_perturbation_estimate K₀ K L c hbase hclose w hw)
    (a • u) v hfix hv hnorm).symm

end DefocusingNLS

end OAI
