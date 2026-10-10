import Mathlib
import OAI.Geometry.SmoothYau.Estimates.PhysicalFiniteSuperpositionComplete

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples
theorem actual_metric_superposition_complete
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (m D : ℕ) :
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
    ∃ T > 0, ∃ c > 0, ∃ M₀ > 0, ∃ C > 0, ∃ r₀ > 0, ∃ rₑ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ (z : metricFrameSet g K → Fin 3 → Fin 3 → ℂ)
        (U : metricFrameSet g K → Fin 3 → NormalWaveSpace → ℂ),
        (∀ q ℓ, (∑ i, z q ℓ i*z q ℓ i = -1) ∧
          ‖phaseRealVector (z q ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
        (∀ q ℓ, ContDiff ℝ ∞ (U q ℓ) ∧ HasCompactSupport (U q ℓ) ∧
          U q ℓ q.1.1 = Complex.exp ((n : ℂ)*(φ q.1.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U q ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ q ℓ (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt n)⁻¹ ≤ r →
          ∀ x y : NormalWaveSpace, ‖x-q.1.1‖ ≤ r → ‖y-q.1.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ‖U q ℓ y-(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z q ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U q ℓ x‖ ≤
          (M₀*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z q ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U q ℓ x‖) ∧
        ∀ (I : Type) [Fintype I] (p : I → metricFrameSet g K)
          (w : NormalWaveSpace → ℝ), ContDiff ℝ ∞ w → ∀ i₀ : I,
        ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
        let y := normalCoordinateMap g (p i₀) x
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
        let W := Real.exp (n*φ (normalWaveEquiv y))+R
        ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
            (fun i ℓ => U (p i) ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
          ENNReal.ofReal (C*n^28*r^4) := by
  apply physical_finite_superposition_complete g φ hφ hK _ _ m D
  · intro q hq ha
    apply actualProfileStrict_normal_direction g hφ hq
    exact hnc q.1 hq.1 (mt (normalWaveProfile_gradient_zero_iff g hφ hq).mpr ha)
  · intro q hq ha
    exact actualCriticalPlane_normal g hφ hq (hcrit q.1 hq.1
      ((normalWaveProfile_gradient_zero_iff g hφ hq).mp ha))

end YauCounterexamples
end

end OAI
