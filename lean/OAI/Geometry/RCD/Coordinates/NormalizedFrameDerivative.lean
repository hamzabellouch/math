import OAI.Geometry.RCD.Coordinates.FramePathEndpointEnergy

namespace OAI

/-! # The scalar velocity residual in radius-normalized coordinates -/

noncomputable section
namespace RegularPointCoordinates

theorem normalized_frame_derivative {n : ℕ} {f : ℝ → ℝ} {c : Fin n → ℝ → ℝ}
    (b : Fin n → ℝ) {t r D E : ℝ} (hr : 0<r) (hD : 0≤D) (hDr : D≤r) (hE : 0≤E)
    (hf : DifferentiableAt ℝ f t) (hc : ∀ i, DifferentiableAt ℝ (c i) t)
    (he : (deriv f t-∑ i, b i*deriv (c i) t)^2≤D^2*E) :
    (deriv (fun s => f s/r) t-∑ i, b i*deriv (fun s => c i s/r) t)^2≤E := by
  rw [(hf.hasDerivAt.div_const r).deriv]
  simp_rw [fun i => ((hc i).hasDerivAt.div_const r).deriv]
  have heq : deriv f t/r-∑ i, b i*(deriv (c i) t/r)=
      (deriv f t-∑ i, b i*deriv (c i) t)/r := by
    simp only [mul_div_assoc,Finset.sum_div,sub_div]
  rw [heq,div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD hDr 2) hE
  exact he.trans (by simpa only [mul_comm] using hh)

end RegularPointCoordinates

end

end OAI
