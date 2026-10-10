import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ComplexWaveJetGerm
import OAI.Geometry.SmoothYau.Smoothness.NormalCoordinateMap

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples

theorem physical_finite_superposition_smallBall
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (hnc : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 ≠ 0 → ∃ v,
      inner ℝ (gradient (normalWaveProfile g φ q) 0) v = 0 ∧
      ‖v‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
      0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
        (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) v v)
    (hcrit : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 = 0 →
      ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v)
    (m D : ℕ) :
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
    ∃ T > 0, ∃ C > 0, ∃ r₀ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ U : metricFrameSet g K → Fin 3 → NormalWaveSpace → ℂ,
        (∀ q ℓ, ContDiff ℝ ∞ (U q ℓ) ∧ HasCompactSupport (U q ℓ) ∧
          U q ℓ q.1.1 = Complex.exp ((n : ℂ)*(φ q.1.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U q ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
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
  classical
  obtain ⟨e,he,ρ,hρ,hfam⟩ := physical_triple_packets_with_smallBall g φ hφ hK hnc hcrit m D
  obtain ⟨M,hM,hMb⟩ := normalCoordinateMap_derivative_bound g hK
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨ρ,hρ,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨T,hT,C₀,hC₀,r₀,hr₀,N,hN,hdata⟩ := hfam ζ hζ hcζ hsζ hζ0
  refine ⟨T,hT,C₀*M^4,mul_pos hC₀ (pow_pos hM0 _),r₀,hr₀,N,hN,?_⟩
  intro n hn
  choose U hU hlaw using (fun q : metricFrameSet g K => hdata q q.property n hn)
  refine ⟨U,hU,?_⟩
  intro I _ p w hw i₀ x hxr hxn
  dsimp only
  intro R hR0 hR r hr
  let F := normalCoordinateMap g (p i₀)
  have hF : ContDiff ℝ ∞ F := (contDiff_normalCoordinateMap g).comp
    (contDiff_const.prodMk contDiff_id)
  have hx1 : ‖x‖ ≤ 1 := hxn.trans (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (hN.trans hn))
  have hfe (t : Fin 3 → ℝ) : normalWaveEquiv (F t) = e (p i₀) (normalWaveEquiv t) := by
    simp only [F,normalCoordinateMap,ContinuousLinearEquiv.apply_symm_apply,he]
  let W := Real.exp (n*φ (normalWaveEquiv (F x)))+R
  have hR' : R ≤ n^6*Real.exp (n*φ (e (p i₀) (normalWaveEquiv x))) := by
    simpa only [←hfe] using hR
  have hsmall := hlaw (p i₀) x hxr hxn R hR0 hR'
  have h := finite_superposition_pullback_smallBall n W (w ∘ normalWaveEquiv)
    (fun i ℓ => U (p i) ℓ ∘ normalWaveEquiv) (hw.comp normalWaveEquiv.contDiff)
    (fun i ℓ => (hU (p i) ℓ).1.comp normalWaveEquiv.contDiff) F hF x M
    (hMb (p i₀) (p i₀).property x hx1) i₀ r
    (ENNReal.ofReal (C₀*n^28*(M*r)^4)) ?_
  · convert h using 1
    congr 1
    ring
  · intro Ω _ μ _ noise hnoise
    have hs := hsmall Ω μ noise hnoise (M*r) (mul_nonneg hM0.le hr)
    convert hs using 1
    simp only [Function.comp_def,hfe,W]

end YauCounterexamples
end

end OAI
