import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.CenteredNormalInverseFderiv
import OAI.Geometry.SmoothYau.Smoothness.FrameInverseApply

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples

theorem uniform_physical_waves_with_endpoint_ratios
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
      ∃ T > 0, ∃ r₀ > 0, ∃ C₀ > 0,
      ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix),
        ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        (∀ n : ℝ, 1 ≤ n →
          ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
          ContDiff ℝ ∞ (U q z Q n) ∧ HasCompactSupport (U q z Q n) ∧
          U q z Q n q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q z Q n) y‖ ≤ T*n^k*Real.exp (n*φ y) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q z Q n) w +
              (n : ℂ)*((n : ℂ)+2)*U q z Q n w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → 0 ≤ δ →
          ∀ x y : NormalWaveSpace, ‖x-q.1‖ ≤ r → ‖y-q.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ∀ L : NormalWaveSpace →L[ℝ] ℂ, ‖normalPhaseCovector q z-L‖ ≤ δ → C₀*r+δ ≤ 1/2 →
          ‖U q z Q n y-Complex.exp ((n : ℂ)*L (y-x))*U q z Q n x‖ ≤
            (10*(C₀*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*U q z Q n x‖) := by
  obtain ⟨A,b,e,hA,hb,hA0,hAd,he,hfactory⟩ := uniform_physical_waves_with_coordinates g φ hφ hK
  obtain ⟨ρ,hρ,hsource,hfactory⟩ := hfactory B C hκ m D
  obtain ⟨ri,hri,ψ,hψ,hψ0,hψd,hnear⟩ := centered_inverse_for_normal_charts g hK e he hρ hsource
  refine ⟨ρ,hρ,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨U,T,hT,hU,hUb⟩ := hfactory ζ hζ hcζ hsζ hζ0
  obtain ⟨re,hre,C₀,hC₀,hend⟩ := normal_family_composed_endpoint_ratio g φ hφ hK A b hA hb hA0 hAd
    ψ hψ hψ0 B C κ ζ hζ0 m D
  refine ⟨U,T,hT,min ri re,lt_min hri hre,C₀,hC₀,?_⟩
  intro q hq z Q hz hnQ hQ
  refine ⟨hUb q hq z Q hz hnQ hQ,?_⟩
  intro n r δ hn hr hrr hδ x y hx hy hsep L hL heps
  have hrri : r < ri := hrr.trans_le (min_le_left ri re)
  have hrre : r < re := hrr.trans_le (min_le_right ri re)
  have hEq (v : NormalWaveSpace) (hv : ‖v-q.1‖ ≤ r) :
      U q z Q n v = normalFamilyWave g φ A b q z Q ζ m D n
        (normalWaveEquiv.symm (ψ (q,v-q.1))) := by
    have ht : v-q.1 ∈ Metric.ball (0 : NormalWaveSpace) ri := by
      simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_lt hrri
    have hh := hnear q hq (v-q.1) ht
    have hu := hU q z Q n (normalWaveEquiv.symm (ψ (q,v-q.1)))
      (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh.1)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,hh.2.1,add_sub_cancel] using hu
  have hder := normalFamilyPhase_centered_fderiv g φ A hA hq (hA0 q hq) (hAd q hq)
    (fun t => ψ (q,t)) (hψ.comp (contDiff_const.prodMk contDiff_id)) (hψ0 q hq) (hψd q hq)
    z Q hnQ hQ m D
  have hbound := hend q hq z Q hz hnQ hQ n r δ hn hr hrre hδ (x-q.1) (y-q.1) hx hy
    (by simpa only [sub_sub_sub_cancel_right] using hsep) L (by rwa [hder]) heps
  simpa only [←hEq x hx,←hEq y hy,sub_sub_sub_cancel_right] using hbound
end YauCounterexamples
end

end OAI
