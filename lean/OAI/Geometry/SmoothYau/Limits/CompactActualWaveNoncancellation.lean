import Mathlib
import OAI.Geometry.SmoothYau.Estimates.UniformPolynomialSmallBall
import OAI.Geometry.SmoothYau.Geometry.ActualMetricSuperpositionSmallBall
import OAI.Geometry.SmoothYau.Geometry.MetricCenterPolynomialNetCoverage
import OAI.Geometry.SmoothYau.Smoothness.ExistsSmoothComplexCutoff

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
open Set
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_metric_wave_law
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (m D : ℕ) :
    ∃ T > 0, ∃ C > 0, ∃ Q > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
      ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
        (t.card : ℝ) ≤ Q*n^3 ∧
        (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
          U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
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
  obtain ⟨ρ,hρ,hfamily⟩ := actual_metric_superposition_smallBall g φ hφ hK hnc hcrit m D
  obtain ⟨ζ,hζ,hζc,hζs,hζ0⟩ := exists_smooth_complex_cutoff ρ hρ
  obtain ⟨T,hT,C,hC,r₀,hr₀,N,hN,hdata⟩ := hfamily ζ hζ hζc hζs hζ0
  obtain ⟨Q,hQ,hnet⟩ := metric_center_polynomial_net g hK r₀ hr₀
  refine ⟨T,hT,C,hC,Q,hQ,N,hN,?_⟩
  intro n hn
  obtain ⟨U,hU,hlaw⟩ := hdata n hn
  obtain ⟨t,p,ht,hcover⟩ := hnet n (hN.trans hn)
  refine ⟨t,p,(fun i ℓ => U (p i) ℓ),ht,(fun i ℓ => hU (p i) ℓ),?_⟩
  intro w hw y hy R hR0 hR
  dsimp only
  intro r hr
  obtain ⟨i,x,hxr,hxn,hxy⟩ := hcover y hy
  have h := hlaw t p w hw i x hxr hxn
  dsimp only at h
  rw [hxy] at h
  exact h R hR0 hR r hr


end

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
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_wave_noncancellation
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (m D : ℕ) (T₀ H : ℝ) (hT₀ : 0 ≤ T₀) (hH : 0 ≤ H) :
    ∃ T > 0, ∃ A > 0, ∃ Q > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
      ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
        (t.card : ℝ) ≤ Q*n^3 ∧
        (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
          U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ max m 2,
            ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | (∃ i ℓ, n < ‖γ i ℓ‖) ∨ ∃ y ∈ E,
            ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
              (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ < 1/n^110} ≤
          ENNReal.ofReal (A/n^5) := by
  classical
  obtain ⟨T,hT,C,hC,Q,hQ,N,hN,hdata⟩ :=
    compact_actual_metric_wave_law g φ hφ hK hnc hcrit (max m 2) D
  obtain ⟨B,hB,hBK⟩ := (hK.image normalWaveEquiv.symm.continuous).isBounded.exists_pos_norm_le
  obtain ⟨A,hA,hNet⟩ := gaussian_uniform_polynomial_smallBall B C Q hB hC hQ
  let T' := T*(max 1 ‖normalWaveEquiv.toContinuousLinearMap‖)^2
  have hT' : 0 ≤ T' := by dsimp [T']; positivity
  let L := (T₀+3*Q*T')*(1+H)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨T,hT,A,hA,Q,hQ,max N L,le_max_of_le_left hN,?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := hN.trans hnN
  have hnL : L ≤ n^4 := ((le_max_right N L).trans hn).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1 ≤ 4 by omega))
  obtain ⟨t,p,U,ht,hU,hlaw⟩ := hdata n hnN
  refine ⟨t,p,U,ht,hU,?_⟩
  intro S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog
  let U' : t → Fin 3 → (Fin 3 → ℝ) → ℂ := fun i ℓ => U i ℓ ∘ normalWaveEquiv
  have hU' (i) (ℓ) : ContDiff ℝ ∞ (U' i ℓ) := (hU i ℓ).1.comp normalWaveEquiv.contDiff
  have hw' : ContDiff ℝ ∞ (w ∘ normalWaveEquiv) := hw.comp normalWaveEquiv.contDiff
  have hcard : (Fintype.card t : ℝ) ≤ Q*n^3 := by simpa using ht
  refine hNet t (fun γ y => realWaveJet n (W y)
    (finiteWaveSuperposition (w ∘ normalWaveEquiv) U' γ) y) E n L
    hn1 hL hnL hcard (fun y hy => hBK y (hEK hy)) ?_ ?_
  · intro γ hγ x hx y hy
    apply finiteWaveSuperposition_normalized_lipschitz hS hw' hU' hW hW0 γ
      hn1 hQ.le hT' hT₀ hH hcard hγ hwbound ?_ hlog x y (hES hx) (hES hy)
    intro z hz j hj i ℓ
    have hb := physical_packet_low_derivative (hU i ℓ).1 (zero_le_one.trans hn1)
      hT.le (Real.exp_pos _).le hj z ((hU i ℓ).2.2.2 _ j (hj.trans (le_max_right _ _))).1
    exact hb.trans (mul_le_mul_of_nonneg_left (hWlower z hz) (by positivity))
  · intro y hy r hr
    let R := W y-Real.exp (n*φ (normalWaveEquiv y))
    have hR : 0 ≤ R := sub_nonneg.mpr (hWlower y (hES hy))
    have hRcap : R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) := by
      have := hWupper y hy
      dsimp [R]; nlinarith
    have he : Real.exp (n*φ (normalWaveEquiv y))+R = W y := by dsimp [R]; ring
    have hh := hlaw w hw y (hEK hy) R hR hRcap r hr
    rw [he] at hh
    exact hh



end YauCounterexamples
end

end OAI
