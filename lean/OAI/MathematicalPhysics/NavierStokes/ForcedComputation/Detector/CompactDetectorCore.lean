import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorViscosityObservation

namespace OAI

/-! The injection, stirring and waiting argument for an arbitrary planar
processor at a fixed reference center. Both numerical pairs use the same
prescribed program. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

def DetectorPair (d H : ℝ) : Prop :=
  (d = 1 / 32 ∧ H = 1000000000) ∨ (d = 1 / 16 ∧ H = 100000000)

theorem DetectorPair.clearance {d H : ℝ} (h : DetectorPair d H) : 1 / 16 ≤ 2 * d := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

/-- The scalar construction and its two observation implications do not
depend on a machine encoding or on the geometry of a particular target. -/
theorem fixed_center_compact_detector (hE : TorusScalarExistence) (hK : TorusHeatInput)
    {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (hp : ∀ s, PlanePeriodic (V s))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (hΨ : IsPlanarTransition V Ψ) (hv : PlanarVariations V Ψ)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (L : ℕ) (hL : 0 < L)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    (h₂ : ∀ s x, ‖fderiv ℝ (fderiv ℝ (euclideanMap (V s))) x‖ ≤ (L : ℝ)) :
    ∃ w : ℝ → Plane → ℝ,
      GlobalTorusScalarSolution 1 (detectorDrift V detectorBumpDerivativeBound L)
        (detectorSource detectorBumpDerivativeBound L) w (fun _ => 0) ∧
      ContDiff ℝ ∞ (Function.uncurry w) ∧ (∀ t x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → scalarMass w t ≤ (massBound L : ℝ)) ∧
      (massBound L : ℝ) < 1 / 100000000000 ∧
      ∀ ν : ℝ, 0 < ν →
        IsClassicalSolution 1 ν (detectorViscosityForce V detectorBumpDerivativeBound L ν)
          (triangularVelocity (viscosityDrift ν (detectorDrift V detectorBumpDerivativeBound L))
            (viscosityScalar ν w)) (fun _ => 0) ∧
        (∀ u p, IsClassicalSolution 1 ν
            (detectorViscosityForce V detectorBumpDerivativeBound L ν) u p →
          ∀ t, 0 ≤ t → ∀ x, u (t, x) =
            triangularVelocity (viscosityDrift ν (detectorDrift V detectorBumpDerivativeBound L))
              (viscosityScalar ν w) (t, x) ∧ p (t, x) = 0) ∧
        ∀ (E : Set Plane) (d H : ℝ), DetectorPair d H →
          ((∃ k : ℕ, Ψ 0 k ![1 / 4, 1 / 4] ∈ E) →
            ∃ t, 0 ≤ t ∧ ∃ x ∈ E, 1 / 2 < viscosityScalar ν w t x) ∧
          ((∀ s, 0 ≤ s → ∀ x ∈ E,
              2 * d ≤ torusNorm (Ψ 0 s ![1 / 4, 1 / 4] - x)) →
            ∀ t, 0 ≤ t → ∀ x ∈ E, viscosityScalar ν w t x < 1 / 2) := by
  obtain ⟨w, hs, hw, hwp, hn, _⟩ := detectorScalar_exists hE hV hp detectorBumpDerivativeBound L
  have hVs (s : ℝ) : ContDiff ℝ ∞ (V s) :=
    hV.comp (show ContDiff ℝ ∞ (fun x : Plane => (s, x)) from
      contDiff_const.prodMk contDiff_id)
  have hlap (n : ℕ) (t : ℝ)
      (_ht : t ∈ Icc (0 : ℝ) (2 * (duration detectorBumpDerivativeBound L n : ℝ)))
      (x : Plane) :
      |scalarLaplacian (detectorReference Ψ detectorBumpDerivativeBound L n
        (2 * ((n : ℝ) + 1) + t)) x| ≤
          (laplacianBound detectorBumpDerivativeBound L n : ℝ) :=
    detectorReference_laplacian_bound hv hVs hback L hL h₁ h₂ n _ x
  refine ⟨w, hs, hw, hn,
    fun t ht => detector_scalar_mass_bound hV hp hdiv detectorBumpDerivativeBound L hs hw ht,
    (massBound_real_small L).2, fun ν hν => ?_⟩
  have hu := detectorViscosity_solution hV hp hdiv detectorBumpDerivativeBound L hs hw hwp hν
  refine ⟨hu, finite_time_classical_unique (by norm_num) hν.le hu, fun E d H hpair => ?_⟩
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨t, ht, hobs⟩ := detectorBurst_detects hΨ hp hback detectorBumpDerivativeBound L k
      hs hw (hlap k) (detector_old_mass_margin L).le
      (detector_scalar_at_start_bound hK hV hp hdiv detectorBumpDerivativeBound L hs hw k)
      (Nat.cast_nonneg k) (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
    have he : ν * (t / ν) = t := by field_simp [hν.ne']
    exact ⟨t / ν, div_nonneg ht hν.le, Ψ 0 k ![1 / 4, 1 / 4], hk,
      by simpa only [viscosityScalar, he] using hobs⟩
  · intro hfar t ht x hx
    exact detector_negative_all_time hK hΨ hv hV hp hdiv hback detectorBumpDerivativeBound L h₁
      hs hw hlap (fun s hs' y hy => hpair.clearance.trans (hfar s hs' y hy))
      (mul_nonneg hν.le ht) hx

end ForcedComputation.VelocityDetector

end

end OAI
