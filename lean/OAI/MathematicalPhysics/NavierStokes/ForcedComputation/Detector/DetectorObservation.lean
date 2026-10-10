import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorNegative
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularForce

namespace OAI

/-! The analytic detector assembly. Published scalar existence and heat
inputs are explicit, as are the smooth-dependence inputs for the given
planar flow. The quantitative comparison and observation are proved here. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem detector_observation (hE : TorusScalarExistence) (hK : TorusHeatInput)
    {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition V Ψ) (hv : PlanarVariations V Ψ)
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (hp : ∀ s, PlanePeriodic (V s))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (L : ℕ) (hL : 0 < L)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    (h₂ : ∀ s x, ‖fderiv ℝ (fderiv ℝ (euclideanMap (V s))) x‖ ≤ (L : ℝ))
    (E : Set Plane) :
    ∃ w : ℝ → Plane → ℝ,
      GlobalTorusScalarSolution 1 (detectorDrift V detectorBumpDerivativeBound L)
        (detectorSource detectorBumpDerivativeBound L) w (fun _ => 0) ∧
      ContDiff ℝ ∞ (Function.uncurry w) ∧
      (∀ t x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → scalarMass w t ≤ (massBound L : ℝ)) ∧
      IsClassicalSolution 1 1 (detectorForce V detectorBumpDerivativeBound L)
        (triangularVelocity (detectorDrift V detectorBumpDerivativeBound L) w) (fun _ => 0) ∧
      (∀ u p, IsClassicalSolution 1 1 (detectorForce V detectorBumpDerivativeBound L) u p →
        ∀ t, 0 ≤ t → ∀ x,
          u (t, x) = triangularVelocity (detectorDrift V detectorBumpDerivativeBound L)
            w (t, x) ∧ p (t, x) = 0) ∧
      (∀ k : ℕ, Ψ 0 k ![1 / 4, 1 / 4] ∈ E →
        ∃ t, 0 ≤ t ∧ ∃ x ∈ E, 1 / 2 < w t x) ∧
      ((∀ s, 0 ≤ s → ∀ x ∈ E, 1 / 16 ≤ torusNorm (Ψ 0 s ![1 / 4, 1 / 4] - x)) →
        ∀ t, 0 ≤ t → ∀ x ∈ E, w t x < 1 / 2) := by
  obtain ⟨w, hs, hw, hn, hfluid, huniq⟩ :=
    detectorFluid_exists hE hV hp hdiv detectorBumpDerivativeBound L
  have hlap (n : ℕ) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ)
      (2 * (duration detectorBumpDerivativeBound L n : ℝ))) (x : Plane) :
      |scalarLaplacian (detectorReference Ψ detectorBumpDerivativeBound L n
        (2 * ((n : ℝ) + 1) + t)) x| ≤
          (laplacianBound detectorBumpDerivativeBound L n : ℝ) :=
    detectorReference_laplacian_bound hv
      (fun s => hV.comp (contDiff_const.prodMk contDiff_id)) hback L hL h₁ h₂ n _ x
  refine ⟨w, hs, hw, hn, ?_, hfluid, huniq, ?_, ?_⟩
  · intro t ht
    exact detector_scalar_mass_bound hV hp hdiv detectorBumpDerivativeBound L hs hw ht
  · intro k hk
    obtain ⟨t, ht, hh⟩ := detectorBurst_detects hΨ hp hback detectorBumpDerivativeBound L k
      hs hw (hlap k) (detector_old_mass_margin L).le
      (detector_scalar_at_start_bound hK hV hp hdiv detectorBumpDerivativeBound L hs hw k)
      (Nat.cast_nonneg k) (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
    exact ⟨t, ht, _, hk, hh⟩
  · intro hfar t ht x hx
    exact detector_negative_all_time hK hΨ hv hV hp hdiv hback detectorBumpDerivativeBound L
      h₁ hs hw hlap hfar ht hx

end ForcedComputation.VelocityDetector

end

end OAI
