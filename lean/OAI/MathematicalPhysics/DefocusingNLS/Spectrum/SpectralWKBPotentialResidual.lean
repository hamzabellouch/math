import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationWKB

namespace OAI

/-! The WKB residual written in terms of derivatives of the squared momentum.
These are exactly the two terms integrated away from a turning point. -/

namespace DefocusingNLS

theorem spectralWKB_potential_residual (p d e : ℂ) (hp : p≠0) :
    homogeneousSpectralWKBResidual p (d/(2*p)) (e/(2*p)-d^2/(4*p^3))=
      (5/16 : ℂ)*d^2/p^4-e/(4*p^2) := by
  dsimp only [homogeneousSpectralWKBResidual]
  field_simp [hp]
  ring

theorem spectralWKB_potential_residual_norm (p d e : ℂ) (hp : p≠0) :
    ‖homogeneousSpectralWKBResidual p (d/(2*p)) (e/(2*p)-d^2/(4*p^3))‖≤
      (5/16 : ℝ)*‖d‖^2/‖p‖^4+‖e‖/(4*‖p‖^2) := by
  rw [spectralWKB_potential_residual p d e hp]
  have hb := norm_sub_le ((5/16 : ℂ)*d^2/p^4) (e/(4*p^2))
  norm_num only [norm_div,norm_mul,norm_pow,Complex.norm_ofNat] at hb
  exact hb

theorem spectralWKB_potential_residual_weighted (p d e : ℂ) (k : ℝ)
    (hk : 0<k) (hkp : k≤‖p‖) :
    ‖homogeneousSpectralWKBResidual p (d/(2*p)) (e/(2*p)-d^2/(4*p^3))‖/‖p‖≤
      (5/16 : ℝ)*‖d‖^2/k^5+‖e‖/(4*k^3) := by
  have hp0 : 0<‖p‖ := hk.trans_le hkp
  calc
    _ ≤ ((5/16 : ℝ)*‖d‖^2/‖p‖^4+‖e‖/(4*‖p‖^2))/‖p‖ :=
      div_le_div_of_nonneg_right (spectralWKB_potential_residual_norm p d e (norm_pos_iff.mp hp0)) hp0.le
    _ = (5/16 : ℝ)*‖d‖^2/‖p‖^5+‖e‖/(4*‖p‖^3) := by field_simp
    _ ≤ _ := by gcongr

end DefocusingNLS

end OAI
