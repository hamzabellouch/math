import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorForceTranslation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorSupport

namespace OAI

/-! The general-center injection, stirring and waiting theorem, including
both numerical pairs and the input-relative effective force.  The scalar
existence, heat estimate and smooth-dependence inputs remain explicit. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CompactCenter
open ShearFlows Set
open scoped ContDiff

/-- The prescribed periodic planar processor and its effective derivative
data.  The force compiler invokes only this input oracle. -/
structure ProcessorInput (V : ℝ → Plane → Plane) where
  smooth : ContDiff ℝ ∞ (Function.uncurry V)
  spatial_periodic : ∀ s, PlanePeriodic (V s)
  divergence_zero : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0
  time_periodic : ∀ s x, V (s + 1) x = V s x
  phase_collar : ∃ ε : ℝ, 0 < ε ∧ ∀ s, |s| < ε → ∀ x, V s x = 0
  oracle : PlanarJetOracle (CompactProgram.components V)

theorem third_component (a : ℝ → Plane → Plane) (w : ℝ → Plane → ℝ)
    (t : ℝ) (x : Plane) (z : ℝ) :
    triangularVelocity a w (t, atHeight x z) 2 = w t x := by
  rw [triangularVelocity, triangularLift_eq, atHeight_horizontal]
  rfl

/-- Injection, stirring and waiting. The same prescribed force works for
either quantitative `(d,H)` pair. -/
theorem compact_detector (hE : TorusScalarExistence) (hK : TorusHeatInput)
    {V : ℝ → Plane → Plane} (hV : ProcessorInput V)
    (Ψ : ℝ → ℝ → Plane → Plane) (hΨ : IsPlanarTransition V Ψ)
    (hv : PlanarVariations V Ψ)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (L : ℕ) (hL : 0 < L)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    (h₂ : ∀ s x, ‖fderiv ℝ (fderiv ℝ (euclideanMap (V s))) x‖ ≤ (L : ℝ))
    (p : Plane) (b : ℕ → RationalSpaceTime)
    (hb : IsFastName b (shiftSpaceTime (centerShift p))) :
    let C := detectorBumpDerivativeBound
    let K := processorSupport V ∪ injectionNeighborhood p
    IsClosed K ∧ p ∈ injectionNeighborhood p ∧
    ∃ w : ℝ → Plane → ℝ,
      ContDiff ℝ ∞ (Function.uncurry w) ∧ (∀ t x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → scalarMass w t ≤ (massBound L : ℝ)) ∧
      (massBound L : ℝ) < 1 / 100000000000 ∧
      ∀ ν : ℝ, 0 < ν →
        let u := triangularVelocity (viscosityDrift ν (centeredDrift V p C L)) (viscosityScalar ν w)
        ContDiff ℝ ∞ (centeredForce V p C L ν) ∧ SpatiallyPeriodic 1 (centeredForce V p C L ν) ∧
        ContDiff ℝ ∞ u ∧ IsClassicalSolution 1 ν (centeredForce V p C L ν) u (fun _ => 0) ∧
        (∀ u' q, IsClassicalSolution 1 ν (centeredForce V p C L ν) u' q →
          ∀ t, 0 ≤ t → ∀ x, u' (t, x) = u (t, x) ∧ q (t, x) = 0) ∧
        (∀ t x z, 0 ≤ u (t, atHeight x z) 2) ∧
        (∀ (E : Set Plane) (_hopen : IsOpen E) (d H : ℝ), DetectorPair d H →
          ((∃ k : ℕ, Ψ 0 k p ∈ E) →
            ∃ t, 0 ≤ t ∧ ∃ x ∈ E, ∀ z, 1 / 2 < u (t, atHeight x z) 2) ∧
          ((∀ s, 0 ≤ s → ∀ x ∈ E, 2 * d ≤ torusNorm (Ψ 0 s p - x)) →
            ∀ t, 0 ≤ t → ∀ x ∈ E, ∀ z, u (t, atHeight x z) 2 < 1 / 2)) ∧
        (∀ t x, x ∉ K → ∀ z, centeredForce V p C L ν (t, atHeight x z) = 0) ∧
        (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (c : ℕ → RationalSpaceTime)
          (y : SpaceTime) (ha : IsFastRealName a ν) (hc : IsFastName c y)
          (ε : ℚ) (hε : 0 < ε),
          ‖mixedDerivative (centeredForce V p C L ν) α y -
            rationalVector (evaluateCenteredForce hV.smooth hV.oracle p b hb C L
              α a c ha hc ε hε)‖ ≤ (ε : ℝ)) ∧
        (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (_ha : IsFastRealName a ν)
          (T : ℚ) (y : SpaceTime), 0 ≤ y.1 → y.1 ≤ (T : ℝ) →
          ‖mixedDerivative (centeredForce V p C L ν) α y‖ ≤
            (centeredForceBound hV.smooth hV.oracle p b hb C L α a T : ℝ)) := by
  dsimp only
  obtain ⟨w, _, hw, hn, hm, hsmall, hνs⟩ := general_center_compact_detector hE hK
    hV.smooth hV.spatial_periodic hV.divergence_zero hΨ hv hback L hL h₁ h₂ p
  refine ⟨isClosed_closure.union (injectionNeighborhood_closed p),
    injectionNeighborhood_contains p, w, hw, hn, hm, hsmall, ?_⟩
  intro ν hν
  obtain ⟨hu, huniq, hobs⟩ := hνs ν hν
  have hA : ContDiff ℝ ∞ (Function.uncurry (centeredDrift V p detectorBumpDerivativeBound L)) := by
    rw [centeredDrift_eq]
    exact detectorDrift_smooth hV.smooth _ _
  have hAp : ∀ t, PlanePeriodic (centeredDrift V p detectorBumpDerivativeBound L t) := by
    rw [centeredDrift_eq]
    exact detectorDrift_periodic hV.spatial_periodic _ _
  have hH := translated_smooth (-centerShift p)
    (detectorSource_smooth detectorBumpDerivativeBound L)
  have hHp := translated_periodic (-centerShift p)
    (detectorSource_periodic detectorBumpDerivativeBound L)
  refine ⟨triangularForce_smooth (viscosityDrift_smooth hA ν) (viscositySource_smooth hH ν) ν,
    triangularForce_periodic (viscosityDrift_smooth hA ν)
      (viscosityDrift_periodic hAp ν) (viscositySource_periodic hHp ν) ν,
    triangularVelocity_smooth (viscosityDrift_smooth hA ν) (viscosityScalar_smooth hw ν),
    hu, huniq, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x z
    rw [third_component]
    exact hn _ _
  · intro E _ d H hpair
    obtain ⟨hpos, hneg⟩ := hobs E d H hpair
    constructor
    · intro he
      obtain ⟨t, ht, x, hx, hh⟩ := hpos he
      exact ⟨t, ht, x, hx, fun z => by simpa only [third_component] using hh⟩
    · intro he t ht x hx z
      simpa only [third_component] using hneg he t ht x hx
  · intro t x hx z
    exact centeredForce_supported hV.smooth p detectorBumpDerivativeBound L ν t hx z
  · intro α a c y ha hc ε hε
    exact evaluateCenteredForce_spec hV.smooth hV.oracle p b hb _ _ α a c ha hc ε hε
  · intro α a ha T y ht hT
    exact centeredForceBound_spec hν hV.smooth hV.oracle p b hb _ _ α ha T ht hT

end ForcedComputation.VelocityDetector.CompactCenter

end

end OAI
