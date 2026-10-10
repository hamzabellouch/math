import OAI.Analysis.PlanarPacking.NormalizedCandidate
import OAI.Analysis.PlanarPacking.GlobalSign

namespace OAI

namespace SharpPlanar
lemma normalizedCandidate_nonpos {x : Plane} (hx : 1≤‖x‖) : normalizedCandidate x≤0 := by
  rw [normalizedCandidate_apply,exactLeft_apply,scaled_radius]
  apply mul_nonpos_of_nonneg_of_nonpos normalizationConstant_pos.le
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  have hs : (1:ℝ)≤‖x‖^2 := by nlinarith [norm_nonneg x]
  have hh:=global_sign_false hs
  rw [exactJet_zero_H₁] at hh
  norm_num at hh
  exact hh
lemma normalizedCandidate_fourier_nonneg (ξ : Plane) : 0≤(fourier normalizedCandidate ξ).re := by
  rw [normalizedCandidate_fourier]
  change 0≤exactRight (scaleFactor⁻¹ • ξ)/exactLeft 0
  apply div_nonneg _ exactLeft_origin_positive.le
  rw [exactRight_apply]
  apply mul_nonneg (Real.exp_pos _).le
  have hh:=global_sign_true (mul_nonneg b_pos.le (sq_nonneg ‖scaleFactor⁻¹ • ξ‖))
  rw [exactJet_zero_H₂] at hh
  simpa only [ite_true,one_mul] using hh
lemma normalizedCandidate_certificate : SharpCertificate normalizedCandidate :=
  ⟨normalizedCandidate_radial,normalizedCandidate_fourier_origin,normalizedCandidate_origin,
    fun ξ => ⟨normalizedCandidate_fourier_real ξ,normalizedCandidate_fourier_nonneg ξ⟩,
    fun _ hx => normalizedCandidate_nonpos hx⟩
end SharpPlanar

/-- A normalized radial Schwartz certificate for the sharp planar packing bound. -/
theorem sharp_fourier_certificate :
    ∃ f : SchwartzMap SharpPlanar.Plane ℝ, SharpPlanar.SharpCertificate f :=
  ⟨SharpPlanar.normalizedCandidate,SharpPlanar.normalizedCandidate_certificate⟩

end OAI
