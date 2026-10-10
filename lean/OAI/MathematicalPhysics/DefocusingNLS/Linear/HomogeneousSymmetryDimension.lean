import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousAngularDimension
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformModeLine

namespace OAI

/-! # Actual contour eigenspaces have the physical symmetry dimensions -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_contour_symmetry_dimensions (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      ∀ (_hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (_hz : radialMatchingMap n z = 0) (N : ℕ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < (N : ℝ))
    (q : HomogeneousY (radialShootingA n) N)
    (_hq : ∀ x : E, homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk q x =
      radialMatchedCartesian n z x)
    (P : (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) →L[ℂ]
      (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
      (n + radialInnerShootingThreshold) q t) P)
    (_hfin : FiniteDimensional ℂ P.range) (G : P.range →L[ℂ] P.range)
    (_hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
        (n + radialInnerShootingThreshold) q) P hcomm t = NormedSpace.exp ((t : ℝ) • G)),
      Module.finrank ℂ (Module.End.eigenspace G.toLinearMap 0) ≤ 1 ∧
      Module.finrank ℂ (Module.End.eigenspace G.toLinearMap 1) ≤ 1 ∧
      Module.finrank ℂ (Module.End.eigenspace G.toLinearMap (1 / 2)) ≤ 12 := by
  filter_upwards [radialMatchedSpectralMode_classification hRou 9 (by omega),
    radialMatched_eventually_all_mode_lines hRou 9 (by omega)] with n hc hline
  intro z hX hz N ha ha1 hk q hq P hcomm hfin G hG
  have hC (ell : ℕ) (lam : ℂ) (hlam : -(1 / 32 : ℝ) ≤ lam.re)
      (hm : Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) 9
        (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) lam)) :
      (ell = 0 ∧ (lam = 0 ∨ lam = 1)) ∨ (ell = 1 ∧ lam = 1 / 2) := by
    have hη : (((ell : ℝ) * (ell + 10) : ℝ) : ℂ) = (ell : ℂ) * (ell + 10) := by push_cast; rfl
    exact hc z hX hz ell lam hlam (by simpa only [hη] using hm)
  have hc0 (ell : ℕ) (hm : Nonempty (RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) 9
      (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) 0)) : ell = 0 := by
    rcases hC ell 0 (by norm_num) hm with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · norm_num at h
  have hc1 (ell : ℕ) (hm : Nonempty (RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) 9
      (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) 1)) : ell = 0 := by
    rcases hC ell 1 (by norm_num) hm with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · norm_num at h
  have hch (ell : ℕ) (hm : Nonempty (RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) 9
      (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) (1 / 2))) : ell = 1 := by
    rcases hC ell (1 / 2) (by norm_num) hm with ⟨_, h | h⟩ | ⟨h, _⟩
    · norm_num at h
    · norm_num at h
    · exact h
  have hspan0 (L : PhysicalRealPolynomial →ₗ[ℝ] ℂ) (hL : ∀ _ : Fin 1, L 1 = 0)
      (p : PhysicalRealPolynomial) (hp : p.IsHomogeneous 0) : L p = 0 :=
    physicalPolynomial_zero_degree_map L (hL 0) p hp
  have hspan1 (L : PhysicalRealPolynomial →ₗ[ℝ] ℂ) (hL : ∀ j : Fin 12, L (MvPolynomial.X j) = 0)
      (p : PhysicalRealPolynomial) (hp : p.IsHomogeneous 1) : L p = 0 :=
    physicalPolynomial_one_degree_map L hL p hp
  refine ⟨?_, ?_, ?_⟩
  · have hb := homogeneous_contour_eigenspace_dimension n z hX hz N ha ha1 hk q hq P hcomm hfin G hG
      0 0 hc0 (hline z hX hz 0 0 (by norm_num)) (fun _ : Fin 1 => 1) hspan0
    simpa using hb
  · have hb := homogeneous_contour_eigenspace_dimension n z hX hz N ha ha1 hk q hq P hcomm hfin G hG
      1 0 hc1 (hline z hX hz 0 1 (by norm_num)) (fun _ : Fin 1 => 1) hspan0
    simpa using hb
  · have hb := homogeneous_contour_eigenspace_dimension n z hX hz N ha ha1 hk q hq P hcomm hfin G hG
      (1 / 2) 1 hch (hline z hX hz 1 (1 / 2) (by norm_num)) MvPolynomial.X hspan1
    simpa using hb

end DefocusingNLS

end OAI
