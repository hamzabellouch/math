import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalOpenStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalCoordinateStableOrbit

namespace OAI

/-! # Openness for the retained physical symmetry coordinates -/

open Set
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Params" => ProfileSymmetryParameters

attribute [local irreducible] HasPhysicalCoordinateStableOrbits HasPhysicalDiagonalFrame
  HasPhysicalCoordinateFrame HasContinuousDiagonalCoordinateOrbits
  HasContinuousCoordinateStableOrbits diagonalRealCoordinates

theorem physicalCoordinateStableOrbits_open
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (hS : HasCartesianSymbol (-2 * a) Q)
    (π : HomogeneousY a k →L[ℝ] V)
    (h : HasPhysicalCoordinateStableOrbits a b k ha ha1 hk m χ hχ Q hQ π) :
    ∃ U : Set FourierL2, U.Nonempty ∧ IsOpen U ∧
      ∀ f ∈ U, HasPhysicalCutoffOrbit a b k ha ha1 hk m χ hχ Q hQ f := by
  unfold HasPhysicalCoordinateStableOrbits at h
  obtain ⟨G, hspan, hspec, F, _, hphys, hframe, hgraph⟩ := h
  unfold HasPhysicalDiagonalFrame HasPhysicalCoordinateFrame at hframe
  obtain ⟨B, hB⟩ := hframe
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let c := diagonalRealCoordinates π G hspan hspec
  let C : Params ≃L[ℝ] c.range := (physicalModulationParameterEquiv b).trans B
  have hC (p : Params) : C p = c.rangeRestrict (F (physicalModulationParameterEquiv b p)) := by
    apply Subtype.ext
    exact hB (physicalModulationParameterEquiv b p)
  unfold HasContinuousDiagonalCoordinateOrbits at hgraph
  exact physical_cutoff_orbit_open_of_frame a b k ha ha1 hk m χ hχ hχzero hχone Q hQ hS
    F hphys c.rangeRestrict C hC hgraph

end DefocusingNLS

end OAI
