import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCompactExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeRootClassification

namespace OAI

/-! On every fixed compact spectral set the only possible large-power
eigenvalues approach the appropriate symmetry values. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSpectralMode_radial_localization (hR : RectangleRouche)
    (N : ℕ) (hN : 7≤N) (K : Set ℂ) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ lam ∈ K, -(1/32 : ℝ)≤lam.re →
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) 0 lam) →
      dist lam 0<ε ∨ dist lam 1<ε := by
  let S := K ∩ {lam : ℂ | ε≤dist lam 0 ∧ ε≤dist lam 1}
  have hS : IsCompact S := hK.inter_right
    ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le continuous_const (continuous_id.dist continuous_const)))
  have he := radialMatchedSpectralMode_compact_exclusion 0 N hN S hS
    (fun z _ hz lam hmem hhalf hzero => by
      rcases (radialFree_phase_scaling_zeros hR (profileMatchingParameter z) hz lam hhalf).mp hzero with
        rfl | rfl
      · exact (not_le_of_gt hε) (by simpa only [dist_self] using hmem.2.1)
      · exact (not_le_of_gt hε) (by simpa only [dist_self] using hmem.2.2))
  filter_upwards [he] with n hn z hX hz lam hlam hhalf hmode
  by_contra h
  push Not at h
  exact hn z hX hz lam ⟨hlam,h⟩ hhalf (by simpa only [Nat.cast_zero,zero_mul] using hmode)

theorem radialMatchedSpectralMode_translation_localization (hR : RectangleRouche)
    (N : ℕ) (hN : 7≤N) (K : Set ℂ) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ lam ∈ K, -(1/32 : ℝ)≤lam.re →
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) 11 lam) → dist lam (1/2)<ε := by
  let S := K ∩ {lam : ℂ | ε≤dist lam (1/2)}
  have hS : IsCompact S := hK.inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have he := radialMatchedSpectralMode_compact_exclusion 1 N hN S hS
    (fun z _ hz lam hmem hhalf hzero => by
      have heq := (radialFree_translation_zero hR (profileMatchingParameter z) hz lam hhalf).mp hzero
      exact (not_le_of_gt hε) (by simpa only [Set.mem_ofPred_eq,heq,dist_self] using hmem.2))
  filter_upwards [he] with n hn z hX hz lam hlam hhalf hmode
  by_contra h
  exact hn z hX hz lam ⟨hlam,le_of_not_gt h⟩ hhalf
    (by simpa only [Nat.cast_one,one_mul,show (1 : ℂ)+10=11 by norm_num] using hmode)

end DefocusingNLS

end OAI
