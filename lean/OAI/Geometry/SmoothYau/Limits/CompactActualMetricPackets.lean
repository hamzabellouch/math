import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ActualMetricSuperpositionComplete
import OAI.Geometry.SmoothYau.Geometry.MetricCenterPolynomialNetCoverage
import OAI.Geometry.SmoothYau.Smoothness.ExistsSmoothComplexCutoff

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples
theorem compact_actual_metric_packets
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (m D : ℕ) :
    ∃ T > 0, ∃ c > 0, ∃ M > 0, ∃ C > 0, ∃ Q > 0, ∃ rₑ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
      ∃ (z : t → Fin 3 → Fin 3 → ℂ) (U : t → Fin 3 → NormalWaveSpace → ℂ),
        (t.card : ℝ) ≤ Q*n^3 ∧
        (∀ y ∈ K, ∃ i : t, n*‖y-(p i).1.1‖ ≤ 1) ∧
        (∀ i ℓ, (∑ j, z i ℓ j*z i ℓ j = -1) ∧
          ‖phaseRealVector (z i ℓ)-gradient (normalWaveProfile g φ (p i)) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
        (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
          U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ i ℓ (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt n)⁻¹ ≤ r →
          ∀ x y : NormalWaveSpace, ‖x-(p i).1.1‖ ≤ r → ‖y-(p i).1.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ‖U i ℓ y-(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector (p i) (z i ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U i ℓ x‖ ≤
          (M*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector (p i) (z i ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U i ℓ x‖) ∧
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ y ∈ normalWaveEquiv.symm '' K,
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
        let W := Real.exp (n*φ (normalWaveEquiv y))+R
        ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
            (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
          ENNReal.ofReal (C*n^28*r^4) := by
  classical
  obtain ⟨ρ,hρ,hfamily⟩ := actual_metric_superposition_complete g φ hφ hK hnc hcrit m D
  obtain ⟨ζ,hζ,hζc,hζs,hζ0⟩ := exists_smooth_complex_cutoff ρ hρ
  obtain ⟨T,hT,c,hc,M,hM,C,hC,r₀,hr₀,rₑ,hrₑ,N,hN,hdata⟩ := hfamily ζ hζ hζc hζs hζ0
  obtain ⟨Q,hQ,hnet⟩ := metric_center_polynomial_net_with_coverage g hK r₀ hr₀
  refine ⟨T,hT,c,hc,M,hM,C,hC,Q,hQ,rₑ,hrₑ,N,hN,?_⟩
  intro n hn
  obtain ⟨z,U,hz,hU,hend,hlaw⟩ := hdata n hn
  obtain ⟨t,p,ht,hcover⟩ := hnet n (hN.trans hn)
  refine ⟨t,p,(fun i ℓ => z (p i) ℓ),(fun i ℓ => U (p i) ℓ),ht,?_,
    (fun i ℓ => hz (p i) ℓ),(fun i ℓ => hU (p i) ℓ),(fun i ℓ => hend (p i) ℓ),?_⟩
  · intro y hy
    obtain ⟨i,x,hxr,hxn,hxy,hnear⟩ := hcover (normalWaveEquiv.symm y) ⟨y,hy,rfl⟩
    exact ⟨i,by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hnear⟩
  intro w hw y hy R hR0 hR
  dsimp only
  intro r hr
  obtain ⟨i,x,hxr,hxn,hxy,hnear⟩ := hcover y hy
  have h := hlaw t p w hw i x hxr hxn
  dsimp only at h
  rw [hxy] at h
  exact h R hR0 hR r hr

end YauCounterexamples
end

end OAI
