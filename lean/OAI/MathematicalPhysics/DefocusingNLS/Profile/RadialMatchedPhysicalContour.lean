import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalSpan
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymmetryProjection
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymmetryDimension
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteSymmetryDimension
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.SymmetryRangeGenerator

namespace OAI

/-! # The actual matched contour consists exactly of the physical fourteen directions -/

open Filter Topology
open scoped NNReal

namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_contour_physical_frame (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      ∀ (_hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
      (_hz : radialMatchingMap n z = 0) (N : ℕ)
      (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < (N : ℝ))
      (q : HomogeneousY (radialShootingA n) N)
      (_hq : ∀ y : E, homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk q y =
        radialMatchedCartesian n z y)
      (P : (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) →L[ℂ]
        (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N)),
      IsIdempotentElem P → ∀ hcomm : ∀ s, Commute
        (homogeneousComplexLinearizedStep (radialShootingA n)
          (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
          (n + radialInnerShootingThreshold) q s) P,
      FiniteDimensional ℂ P.range →
      HasSymmetryRangeGenerator
        (homogeneousComplexLinearizedStep (radialShootingA n)
          (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
          (n + radialInnerShootingThreshold) q) P hcomm →
      ∀ D δ : ℝ, 0 < δ →
      (∀ s : ℝ≥0, ∀ w, P w = 0 →
        ‖homogeneousComplexLinearizedStep (radialShootingA n)
          (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
          (n + radialInnerShootingThreshold) q s w‖ ≤ D * Real.exp (-δ * (s : ℝ)) * ‖w‖) →
      ∃ F : ProfileSymmetryParameters →L[ℝ] HomogeneousY (radialShootingA n) N,
        Function.Injective F ∧
        (∀ p y, homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk (F p) y =
          (p.1 : ℂ) * (Complex.I * radialMatchedCartesian n z y) +
          (p.2.2 : ℂ) * (((radialShootingA n : ℂ) -
            Complex.I * (radialShootingB (profileMatchingParameter z) : ℂ)) * radialMatchedCartesian n z y +
              cartesianTransport (radialMatchedCartesian n z) y) +
            cartesianDerivative p.2.1 (radialMatchedCartesian n z) y) ∧
        Submodule.span ℂ (Set.range (fun p =>
          homogeneousComplexEmbed (radialShootingA n) N ha ha1 hk (F p))) = P.range := by
  filter_upwards [radialMatched_contour_symmetry_dimensions hRou] with n hn
  intro z hX hz N ha ha1 hk q hq P hP hcomm hfin hgen D δ hδ hdecay
  let : FiniteDimensional ℂ P.range := hfin
  obtain ⟨G, hG, hspec, hspan⟩ := hgen
  obtain ⟨h0, h1, hh⟩ := hn z hX hz N ha ha1 hk q hq P hcomm hfin G hG
  have hdim := finite_symmetry_dimension_le G hspec hspan h0 h1 hh
  obtain ⟨F, hF, hphys⟩ := radialMatched_physical_symmetry_frame n z hX hz N ha ha1 hk q hq
  refine ⟨F, hF, hphys, homogeneous_physical_frame_spans _ N ha ha1 hk F hF P ?_ hdim⟩
  exact radialMatched_projection_fixes_physical_frame n z hX hz N ha ha1 hk q hq
    P hP hcomm D δ hδ hdecay F hphys

end DefocusingNLS

end OAI
