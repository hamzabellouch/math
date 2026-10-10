import OAI.Analysis.CircleDomains.Topology.PlanarRectangleGreen
import OAI.Analysis.CircleDomains.Sobolev.PolarDiskIntegral
import OAI.Analysis.CircleDomains.Topology.PolarFormBoundary

namespace OAI

/-! Green's formula on a round disk, proved by polar pullback and the
existing rectangular divergence theorem. No Green input is used. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma roundDiskGreen {P Q : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) {R : ℝ} (hR : 0 < R) :
    planarFormIntegral P Q (unitCircleParam 0 R) =
      ∫ z in Metric.ball (0 : ℂ) R, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  have he := integral_pulledPlanarForm_curl_rectangle hP hQ contDiff_complexPolarSymm
    (0,-Real.pi) (R,Real.pi) ⟨hR.le,by linarith [Real.pi_pos]⟩
  simp only [complexPolarSymm_jacobian] at he
  rw [← planarFormIntegral_circle_eq_polar P Q R] at he
  simp_rw [pulledPolarForm_radius_zero] at he
  simp only [intervalIntegral.integral_zero,sub_zero] at he
  have hseam :
      (∫ s in (0 : ℝ)..R,
        pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (1,0) (s,Real.pi)) =
      ∫ s in (0 : ℝ)..R,
        pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (1,0) (s,-Real.pi) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    simp only [pulledPlanarForm,complexPolarSymm_fderiv]
    simp [Complex.polarCoord_symm_apply]
  rw [hseam,← integral_polar_disk (fun z =>
    (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) R] at he
  linarith

end CircleDomainRigidity

end

end OAI
