import Mathlib
import OAI.Geometry.SmoothYau.Estimates.NormalFamilyCanonicalSmallBall
import OAI.Geometry.SmoothYau.Geometry.UniformPhysicalWavesCoordinates

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
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma complexWaveJet_germ {u v : (Fin 3 → ℝ) → ℂ} {x : Fin 3 → ℝ}
    (h : u =ᶠ[𝓝 x] v) (n : ℝ) (W : ℂ) :
    complexWaveJet n W u x = complexWaveJet n W v x := by
  ext i
  rcases i with i|i
  · simp only [complexWaveJet,Sum.elim_inl,h.eq_of_nhds]
  · simp only [complexWaveJet,Sum.elim_inr,waveDeriv,h.fderiv_eq]

theorem physical_triple_packets_with_smallBall
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
    ∃ (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace),
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
    ∃ T > 0, ∃ C₀ > 0, ∃ r₀ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ q ∈ metricFrameSet g K, ∀ n : ℝ, N ≤ n →
      ∃ U : Fin 3 → NormalWaveSpace → ℂ,
        (∀ ℓ, ContDiff ℝ ∞ (U ℓ) ∧ HasCompactSupport (U ℓ) ∧
          U ℓ q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (e q (normalWaveEquiv x))) →
        let W := Real.exp (n*φ (e q (normalWaveEquiv x)))+R
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
        (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ)
            (fun t => U ℓ (e q (normalWaveEquiv t))) x) v.2+noise v.1 ∈
            Metric.closedBall 0 r} ≤ ENNReal.ofReal (C₀*n^28*r^4) := by
  obtain ⟨A,b,e,hA,hb,hA0,hAd,he,hfactory⟩ := uniform_physical_waves_with_coordinates g φ hφ hK
  obtain ⟨κ,hκ,C,hC,B,hB,hsmall⟩ := normal_family_canonical_smallBall_uniform g φ hφ hK
    A b hA hb hA0 hAd hnc hcrit
  obtain ⟨ρ,hρ,hsrc,hwaves⟩ := hfactory B C hκ m D
  refine ⟨e,he,ρ,hρ,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨U,T,hT,hformula,hest⟩ := hwaves ζ hζ hcζ hsζ hζ0
  obtain ⟨r₁,hr₁,C₀,hC₀,N,hN,hs⟩ := hsmall ζ hζ0 m D
  refine ⟨T,hT,C₀,hC₀,min r₁ ρ,lt_min hr₁ hρ,N,hN,?_⟩
  intro q hq n hn
  obtain ⟨z,Q,hz,hnull,hQ,hdev,hlaw⟩ := hs q hq n hn
  let Z : Fin 3 → NormalWaveSpace → ℂ := fun ℓ => U q (z ℓ) (Q ℓ) n
  refine ⟨Z,(fun ℓ => hest q hq (z ℓ) (Q ℓ) (hz ℓ) (hnull ℓ) (hQ ℓ)
    n (hN.trans hn) (hdev ℓ)),?_⟩
  intro x hx hxn R hR0 hR
  dsimp only
  intro Ω _ μ _ noise hnoise r hr
  have hxsrc : normalWaveEquiv x ∈ (e q).source := hsrc q hq x (hx.trans_le (min_le_right _ _))
  have hjet (ℓ : Fin 3) (W : ℂ) :
      complexWaveJet n W (fun t => Z ℓ (e q (normalWaveEquiv t))) x =
        complexWaveJet n W (normalFamilyWave g φ A b q (z ℓ) (Q ℓ) ζ m D n) x := by
    apply complexWaveJet_germ
    filter_upwards [( (e q).open_source.preimage normalWaveEquiv.continuous).mem_nhds hxsrc] with t ht
    exact hformula q (z ℓ) (Q ℓ) n t ht
  simp_rw [hjet]
  have hR' : R ≤ n^6*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) := by
    simpa only [he,normalWaveProfile] using hR
  simpa only [he,normalWaveProfile] using
    hlaw x (hx.trans_le (min_le_left _ _)) hxn R hR0 hR' Ω μ noise hnoise r hr

end YauCounterexamples

end

end OAI
