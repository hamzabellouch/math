import Mathlib
import OAI.Geometry.SmoothYau.Geometry.UniformCoordinatePacketsCommonSlope2

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
theorem physical_triple_packets_complete_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {V : Set NormalWaveSpace} (hV : IsOpen V) (hKV : K ⊆ V)
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
    ∃ T > 0, ∃ c > 0, ∃ M > 0, ∃ C₀ > 0, ∃ r₀ > 0, ∃ rₑ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ q ∈ metricFrameSet g K, ∀ n : ℝ, N ≤ n →
      ∃ (z : Fin 3 → Fin 3 → ℂ) (U : Fin 3 → NormalWaveSpace → ℂ),
        (∀ ℓ, tsupport (U ℓ) ⊆ V) ∧
        (∀ ℓ, (∑ i, z ℓ i*z ℓ i = -1) ∧
          ‖phaseRealVector (z ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
        (∀ ℓ, ContDiff ℝ ∞ (U ℓ) ∧ HasCompactSupport (U ℓ) ∧
          U ℓ q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ ℓ (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt n)⁻¹ ≤ r →
          ∀ x y : NormalWaveSpace, ‖x-q.1‖ ≤ r → ‖y-q.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ‖U ℓ y-(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U ℓ x‖ ≤
          (M*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U ℓ x‖) ∧
        ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (e q (normalWaveEquiv x))) →
        let W := Real.exp (n*φ (e q (normalWaveEquiv x)))+R
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
        (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ)
            (fun t => U ℓ (e q (normalWaveEquiv t))) x) v.2+noise v.1 ∈
            Metric.closedBall 0 r} ≤ ENNReal.ofReal (C₀*n^28*r^4) := by
  obtain ⟨A,b,e,hA,hb,hA0,hAd,he,hfactory⟩ := uniform_coordinate_packets_common_slope_supported g φ hφ hK hV hKV
  obtain ⟨κ,hκ,C,hC,B,hB,hsmall⟩ := normal_family_canonical_smallBall_uniform g φ hφ hK
    A b hA hb hA0 hAd hnc hcrit
  obtain ⟨ρ,hρ,hsrc,hwaves⟩ := hfactory B C hκ m D
  refine ⟨e,he,ρ,hρ,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨U,T,hT,c,hc,re,hre,M,hM,hSupport,hformula,hest⟩ := hwaves ζ hζ hcζ hsζ hζ0
  obtain ⟨r₁,hr₁,C₀,hC₀,N,hN,hs⟩ := hsmall ζ hζ0 m D
  refine ⟨T,hT,c,hc,M,hM,C₀,hC₀,min r₁ ρ,lt_min hr₁ hρ,re,hre,N,hN,?_⟩
  intro q hq n hn
  obtain ⟨z,Q,hz,hnull,hQ,hdev,hlaw⟩ := hs q hq n hn
  let Z : Fin 3 → NormalWaveSpace → ℂ := fun ℓ => U q (z ℓ) (Q ℓ) n
  refine ⟨z,Z,(fun ℓ => hSupport q hq (z ℓ) (Q ℓ) n),(fun ℓ => ⟨hnull ℓ,hdev ℓ⟩),
    (fun ℓ => (hest q hq (z ℓ) (Q ℓ) (hz ℓ) (hnull ℓ) (hQ ℓ)).1
      n (hN.trans hn) (hdev ℓ)),?_,?_⟩
  · intro ℓ r hr hrr hnr x y hx hy hsep
    exact (hest q hq (z ℓ) (Q ℓ) (hz ℓ) (hnull ℓ) (hQ ℓ)).2 n r
      (hN.trans hn) hr hrr hnr (hdev ℓ) x y hx hy hsep
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

end


open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
theorem physical_finite_superposition_complete_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O)
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
    ∃ T > 0, ∃ c > 0, ∃ M₀ > 0, ∃ C > 0, ∃ r₀ > 0, ∃ rₑ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ (z : metricFrameSet g K → Fin 3 → Fin 3 → ℂ)
        (U : metricFrameSet g K → Fin 3 → NormalWaveSpace → ℂ),
        (∀ q ℓ, tsupport (U q ℓ) ⊆ O) ∧
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
  classical
  obtain ⟨e,he,ρ,hρ,hfam⟩ := physical_triple_packets_complete_supported g φ hφ hK hO hKO hnc hcrit m D
  obtain ⟨M,hM,hMb⟩ := normalCoordinateMap_derivative_bound g hK
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨ρ,hρ,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨T,hT,c,hc,M₀,hM₀,C₀,hC₀,r₀,hr₀,rₑ,hrₑ,N,hN,hdata⟩ := hfam ζ hζ hcζ hsζ hζ0
  refine ⟨T,hT,c,hc,M₀,hM₀,C₀*M^4,mul_pos hC₀ (pow_pos hM0 _),r₀,hr₀,rₑ,hrₑ,N,hN,?_⟩
  intro n hn
  choose z U hSupport hz hU hend hlaw using (fun q : metricFrameSet g K => hdata q q.property n hn)
  refine ⟨z,U,hSupport,hz,hU,hend,?_⟩
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
