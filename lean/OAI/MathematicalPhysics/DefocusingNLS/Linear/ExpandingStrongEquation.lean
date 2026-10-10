import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingModeEquation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.FourierCoordinateDerivative

namespace OAI

/-! # Strong derivatives for the moving-torus equation

The time-dependent Laplacian loses two Sobolev orders.  After this loss,
continuity of the candidate derivative upgrades the Fourier-mode equation
to a strong Hilbert-space equation.
-/

open Set Filter Topology

namespace DefocusingNLS

noncomputable def expandingReducedField (a b L : ℝ) (u r : ℝ → FourierL2) (t : ℝ) : FourierL2 :=
  (-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (u t) +
    (L ^ (-2 : ℝ) * Real.exp (-t)) • lowerSobolevGenerator (u t) +
    lowerSobolevInclusion (r t)

theorem continuousOn_expandingReducedField (a b L : ℝ) (u r : ℝ → FourierL2)
    (J : Set ℝ) (hu : ContinuousOn u J) (hr : ContinuousOn r J) :
    ContinuousOn (expandingReducedField a b L u r) J := by
  have hlow := lowerSobolevInclusion.continuous.comp_continuousOn hu
  have hgen := lowerSobolevGenerator.continuous.comp_continuousOn hu
  have hsource := lowerSobolevInclusion.continuous.comp_continuousOn hr
  have hcoef : Continuous (fun t : ℝ => L ^ (-2 : ℝ) * Real.exp (-t)) := by fun_prop
  exact ((hlow.const_smul (-(a : ℂ) + Complex.I * b)).add
    (hcoef.continuousOn.smul hgen)).add hsource

/-- A continuous Fourier solution of the exact mode equations is a strong solution
in the space with two fewer Sobolev derivatives. -/
theorem hasDerivAt_expandingReducedField (a b L A B : ℝ) (u r : ℝ → FourierL2)
    (hu : ContinuousOn u (Ioo A B)) (hr : ContinuousOn r (Ioo A B))
    (hmode : ∀ t ∈ Ioo A B, ∀ n : frequencyLattice,
      HasDerivAt (fun s => u s n) (expandingModeRate a b L t n * u t n + r t n) t)
    (t : ℝ) (ht : t ∈ Ioo A B) :
    HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (expandingReducedField a b L u r t) t := by
  apply hasDerivAt_fourierL2_of_coordinates _ _ A B t
    (continuousOn_expandingReducedField a b L u r (Ioo A B) hu hr) _ ht
  intro s hs n
  have h := (hmode s hs n).const_mul ((((1 + ‖n‖ ^ 2)⁻¹ : ℝ) : ℂ))
  apply h.congr_deriv
  change (((1 + ‖n‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (expandingModeRate a b L s n * u s n + r s n) =
    (-(a : ℂ) + Complex.I * b) • (lowerSobolevInclusion (u s) n) +
      (L ^ (-2 : ℝ) * Real.exp (-s)) • (lowerSobolevGenerator (u s) n) +
      lowerSobolevInclusion (r s) n
  simp only [smul_eq_mul, Complex.real_smul, lowerSobolevInclusion_apply,
    lowerSobolevGenerator_apply, expandingModeRate]
  push_cast
  ring

end DefocusingNLS

end OAI
