import Mathlib
import OAI.Geometry.SmoothYau.Geometry.UniformCoordinatePacketsEndpointRatios
import OAI.Geometry.SmoothYau.Limits.PhaseImagVector

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem uniform_localized_physical_waves_with_endpoint_ratios
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
      ∃ T > 0, ∃ c > 0, ∃ r₀ > 0, ∃ C₀ > 0,
      ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix),
        ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        (∀ n : ℝ, 1 ≤ n →
          ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
          ContDiff ℝ ∞ (U q z Q n) ∧ HasCompactSupport (U q z Q n) ∧
          U q z Q n q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q z Q n) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q z Q n) w +
              (n : ℂ)*((n : ℂ)+2)*U q z Q n w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → 0 ≤ δ →
          ∀ x y : NormalWaveSpace, ‖x-q.1‖ ≤ r → ‖y-q.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ∀ L : NormalWaveSpace →L[ℝ] ℂ, ‖normalPhaseCovector q z-L‖ ≤ δ → C₀*r+δ ≤ 1/2 →
          ‖U q z Q n y-Complex.exp ((n : ℂ)*L (y-x))*U q z Q n x‖ ≤
            (10*(C₀*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*U q z Q n x‖) := by
  obtain ⟨A,b,e,hA,hb,hA0,hAd,he,hfactory⟩ := uniform_localized_physical_waves_with_coordinates g φ hφ hK
  obtain ⟨ρ,hρ,hsource,hfactory⟩ := hfactory B C hκ m D
  obtain ⟨ri,hri,ψ,hψ,hψ0,hψd,hnear⟩ := centered_inverse_for_normal_charts g hK e he hρ hsource
  refine ⟨ρ,hρ,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨U,T,hT,c,hc,hU,hUb⟩ := hfactory ζ hζ hcζ hsζ hζ0
  obtain ⟨re,hre,C₀,hC₀,hend⟩ := normal_family_composed_endpoint_ratio g φ hφ hK A b hA hb hA0 hAd
    ψ hψ hψ0 B C κ ζ hζ0 m D
  refine ⟨U,T,hT,c,hc,min ri re,lt_min hri hre,C₀,hC₀,?_⟩
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
end



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

def realImagCovector (a b : NormalWaveSpace →L[ℝ] ℝ) : NormalWaveSpace →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp a + Complex.I • (Complex.ofRealCLM.comp b)

lemma covector_real_replacement_error (L : NormalWaveSpace →L[ℝ] ℂ)
    (a : NormalWaveSpace →L[ℝ] ℝ) :
    ‖L-realImagCovector a (Complex.imCLM.comp L)‖ ≤ ‖Complex.reCLM.comp L-a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have heq : (L-realImagCovector a (Complex.imCLM.comp L)) v =
      ((Complex.reCLM.comp L-a) v : ℂ) := by
    apply Complex.ext <;>
      simp [realImagCovector,Complex.mul_re,Complex.mul_im]
  rw [heq,Complex.norm_real]
  exact (Complex.reCLM.comp L-a).le_opNorm v

lemma exp_realImagCovector (a b : NormalWaveSpace →L[ℝ] ℝ) (n : ℝ) (v : NormalWaveSpace) :
    Complex.exp ((n : ℂ)*realImagCovector a b v) =
      (Real.exp (n*a v) : ℂ)*Complex.exp (((n*b v : ℝ) : ℂ)*Complex.I) := by
  have heq : (n : ℂ)*realImagCovector a b v =
      ((n*a v : ℝ) : ℂ)+((n*b v : ℝ) : ℂ)*Complex.I := by
    simp only [realImagCovector,add_apply,ContinuousLinearMap.comp_apply,
      smul_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
    ring
  rw [heq,Complex.exp_add,←Complex.ofReal_exp]

theorem uniform_physical_waves_common_slope
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
      ∃ T > 0, ∃ c > 0, ∃ r₀ > 0, ∃ A > 0,
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
            (A*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
                Complex.exp (((n*normalImagCovector q z (y-x) : ℝ) : ℂ)*Complex.I)*U q z Q n x‖) := by
  obtain ⟨Cs,hCs,hslope⟩ := compact_normal_real_slope_error g hφ hK
  obtain ⟨ρ,hρ,hfactory⟩ := uniform_localized_physical_waves_with_endpoint_ratios g φ hφ hK B C hκ m D
  refine ⟨ρ,hρ,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨U,T,hT,c,hc,re,hre,Ce,hCe,hU⟩ := hfactory ζ hζ hcζ hsζ hζ0
  let A := Ce+2*Cs
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨U,T,hT,c,hc,min re (min 1 (1/(2*A))),
    lt_min hre (lt_min zero_lt_one (by positivity)),10*A,by positivity,?_⟩
  intro q hq z Q hz hnQ hQ
  refine ⟨(hU q hq z Q hz hnQ hQ).1,?_⟩
  intro n r hn hr hrr hnr hlin x y hx hy hsep
  have hrre : r < re := hrr.trans_le (min_le_left _ _)
  have hr1 : r ≤ 1 := (hrr.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hrA : A*r ≤ 1/2 := by
    have hh : r < 1/(2*A) := hrr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (lt_div_iff₀ (show 0 < 2*A by positivity)).mp hh
    nlinarith
  let L := realImagCovector (fderiv ℝ φ x) (normalImagCovector q z)
  have hL : ‖normalPhaseCovector q z-L‖ ≤ 2*Cs*r := by
    have hh := (covector_real_replacement_error (normalPhaseCovector q z) (fderiv ℝ φ x)).trans
      (hslope q hq z x (hx.trans hr1))
    exact hh.trans (by nlinarith [hlin.trans hnr])
  have heps : Ce*r+2*Cs*r ≤ 1/2 := by dsimp [A] at hrA; nlinarith
  have hh := (hU q hq z Q hz hnQ hQ).2 n r (2*Cs*r) hn hr hrre
    (by positivity) x y hx hy hsep L hL heps
  rw [show L = realImagCovector (fderiv ℝ φ x) (normalImagCovector q z) from rfl,
    exp_realImagCovector] at hh
  convert hh using 1
  ring

end YauCounterexamples
end

end OAI
