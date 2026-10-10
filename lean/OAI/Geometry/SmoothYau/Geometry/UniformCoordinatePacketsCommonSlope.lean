import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RealImagCovector

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
namespace YauCounterexamples

theorem uniform_coordinate_packets_common_slope
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    :
    ∃ (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
      (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
      (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace),
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0) ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0) ∧
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
    ∀ (B C : ℝ) {κ : ℝ}, 0 < κ → ∀ m D : ℕ,
    ∃ ρ > 0,
      (∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) ∧
      ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
      ∃ T > 0, ∃ c > 0, ∃ r₀ > 0, ∃ M > 0,
        (∀ q z Q n x, normalWaveEquiv x ∈ (e q).source →
          U q z Q n (e q (normalWaveEquiv x)) = normalFamilyWave g φ A b q z Q ζ m D n x) ∧
      ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix),
        ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        (∀ n : ℝ, 1 ≤ n →
          ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
          ContDiff ℝ ∞ (U q z Q n) ∧ HasCompactSupport (U q z Q n) ∧
          U q z Q n q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q z Q n) y‖ ≤
              T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q z Q n) w +
              (n : ℂ)*((n : ℂ)+2)*U q z Q n w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ (n r : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → (Real.sqrt n)⁻¹ ≤ r →
          ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
          ∀ x y : NormalWaveSpace, ‖x-q.1‖ ≤ r → ‖y-q.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ‖U q z Q n y-
              (Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
                Complex.exp (((n*normalImagCovector q z (y-x) : ℝ) : ℂ)*Complex.I)*U q z Q n x‖ ≤
            (M*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
                Complex.exp (((n*normalImagCovector q z (y-x) : ℝ) : ℂ)*Complex.I)*U q z Q n x‖) := by
  obtain ⟨Cs,hCs,hslope⟩ := compact_normal_real_slope_error g hφ hK
  obtain ⟨A,b,e,hA,hb,hA0,hAd,he,hfact⟩ := uniform_coordinate_packets_with_endpoint_ratios g φ hφ hK
  refine ⟨A,b,e,hA,hb,hA0,hAd,he,?_⟩
  intro B C κ hκ m D
  obtain ⟨ρ,hρ,hsource,hfactory⟩ := hfact B C hκ m D
  refine ⟨ρ,hρ,hsource,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨U,T,hT,c,hc,re,hre,Ce,hCe,hformula,hU⟩ := hfactory ζ hζ hcζ hsζ hζ0
  let M := Ce+2*Cs
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨U,T,hT,c,hc,min re (min 1 (1/(2*M))),
    lt_min hre (lt_min zero_lt_one (by positivity)),10*M,by positivity,hformula,?_⟩
  intro q hq z Q hz hnQ hQ
  refine ⟨(hU q hq z Q hz hnQ hQ).1,?_⟩
  intro n r hn hr hrr hnr hlin x y hx hy hsep
  have hrre : r < re := hrr.trans_le (min_le_left _ _)
  have hr1 : r ≤ 1 := (hrr.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hrM : M*r ≤ 1/2 := by
    have hh : r < 1/(2*M) := hrr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (lt_div_iff₀ (show 0 < 2*M by positivity)).mp hh
    nlinarith
  let L := realImagCovector (fderiv ℝ φ x) (normalImagCovector q z)
  have hL : ‖normalPhaseCovector q z-L‖ ≤ 2*Cs*r := by
    have hh := (covector_real_replacement_error (normalPhaseCovector q z) (fderiv ℝ φ x)).trans
      (hslope q hq z x (hx.trans hr1))
    exact hh.trans (by nlinarith [hlin.trans hnr])
  have heps : Ce*r+2*Cs*r ≤ 1/2 := by dsimp [M] at hrM; nlinarith
  have hh := (hU q hq z Q hz hnQ hQ).2 n r (2*Cs*r) hn hr hrre
    (by positivity) x y hx hy hsep L hL heps
  rw [show L = realImagCovector (fderiv ℝ φ x) (normalImagCovector q z) from rfl,
    exp_realImagCovector] at hh
  convert hh using 1
  ring
end YauCounterexamples
end

end OAI
