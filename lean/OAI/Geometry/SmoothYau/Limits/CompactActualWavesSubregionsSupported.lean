import Mathlib
import OAI.Geometry.SmoothYau.Estimates.FiniteRegionsWaveSignExpectation
import OAI.Geometry.SmoothYau.Estimates.UniformPolynomialSmallBall
import OAI.Geometry.SmoothYau.Smoothness.CompactActualWavesSignJets

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_sign_noncancellation_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ A > 0, ∃ Q > 0,
    ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
    let n := s^4
    ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
    ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
      (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
      (t.card : ℝ) ≤ Q*n^3 ∧
      (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
        U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ max m 2,
          ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
            (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
      (∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
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
          ENNReal.ofReal (A/n^5)) ∧
      ∀ b : NormalWaveSpace → ℝ, (∀ y ∈ K, |b y| ≤ c₀*Real.exp (n*φ y)) →
      ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
      (∀ j, packetAxisShift x n ε ℓ j ∈ K) →
      ∃ j, ENNReal.ofReal p₀ ≤ (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition b U γ x *
          finiteWaveSuperposition b U γ (packetAxisShift x n ε ℓ j) < 0} := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := compact_actual_waves_sign_and_jets_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,T,hT,c,hc,C,hC,Q,hQ,N,hN,hdata⟩ := hdata φ hφ hnc hcrit (max m 2) D
  obtain ⟨B,hB,hBK⟩ := (hK.image normalWaveEquiv.symm.continuous).isBounded.exists_pos_norm_le
  obtain ⟨A,hA,hNet⟩ := gaussian_uniform_polynomial_smallBall B C Q hB hC hQ
  let T' := T*(max 1 ‖normalWaveEquiv.toContinuousLinearMap‖)^2
  have hT' : 0 ≤ T' := by dsimp [T']; positivity
  let L := (T₀+3*Q*T')*(1+H)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨c₀,hc₀,T,hT,c,hc,A,hA,Q,hQ,max N L,le_max_of_le_left hN,?_⟩
  intro s hs
  have hsN : N ≤ s := (le_max_left _ _).trans hs
  have hs1 : 1 ≤ s := (by linarith : (1:ℝ) ≤ N).trans hsN
  have hs4 : s ≤ s^4 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1 ≤ 4 by omega)
  let n := s^4
  have hn1 : 1 ≤ n := hs1.trans hs4
  have hnL : L ≤ n^4 := ((le_max_right N L).trans hs).trans (hs4.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1 ≤ 4 by omega)))
  obtain ⟨t,p,U,hSupport,ht,hU,hlaw,hsign⟩ := hdata s hsN
  refine ⟨t,p,U,hSupport,ht,hU,?_,hsign⟩
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
      hT.le (Real.exp_pos _).le hj z (le_trans ((hU i ℓ).2.2.2 _ j (hj.trans (le_max_right _ _))).1 (by
        have he : Real.exp (-c*n*‖normalWaveEquiv z-(p i).1.1‖^2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have hn0 := zero_le_one.trans hn1
            exact mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hn0) (sq_nonneg _))
        exact mul_le_of_le_one_right (by positivity) he))
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

end


section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_waves_regions_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ Q > 0,
    ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
    let n := s^4
    ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
    ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
      (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
      (t.card : ℝ) ≤ Q*n^3 ∧
      (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
        U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ max m 2,
          ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
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
        (∀ y ∈ K, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (P : Type) [Fintype P] (ℓ q : P → ℝ), (∀ a, 0 ≤ q a) →
        ∀ ν : P → Measure NormalWaveSpace, ∀ _ : ∀ a, IsFiniteMeasure (ν a),
        0 < ∑ a, q a*(ν a univ).toReal →
        (∀ a, ∀ᵐ x ∂ν a, x ∈ K ∧ profileFrequencyScale g φ x ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ x ∧ (∀ j, packetAxisShift x n ε (ℓ a) j ∈ K)) →
        ∃ γ : t → Fin 3 → ℂ, (∀ i j, ‖γ i j‖ ≤ n) ∧
          (∀ y ∈ E, 1/n^110 ≤
            ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
              (fun i j => U i j ∘ normalWaveEquiv) γ) y‖) ∧
          (p₀/2)*(∑ a, q a*(ν a univ).toReal) <
            ∑ a, q a*∑ j : Fin 3, (ν a {x | finiteWaveSuperposition w U γ x *
              finiteWaveSuperposition w U γ (packetAxisShift x n ε (ℓ a) j) < 0}).toReal := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := compact_actual_sign_noncancellation_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,T,hT,c,hc,A,hA,Q,hQ,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m D T₀ H hT₀ hH
  refine ⟨c₀,hc₀,T,hT,c,hc,Q,hQ,max N (12*A/p₀+1),le_max_of_le_left hN,?_⟩
  intro s hs
  have hsN : N ≤ s := (le_max_left _ _).trans hs
  have hs1 : 1 ≤ s := (by linarith : (1:ℝ) ≤ N).trans hsN
  have hs4 : s ≤ s^4 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1 ≤ 4 by omega)
  let n := s^4
  have hn1 : 1 ≤ n := hs1.trans hs4
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  have hAn : A/n^5 < p₀/6 := by
    have hlarge : 12*A/p₀ < n := (lt_add_one _).trans_le (((le_max_right _ _).trans hs).trans hs4)
    have hm := (div_lt_iff₀ hp₀).mp hlarge
    have hd : A/n < p₀/6 := (div_lt_iff₀ hn0).mpr (by nlinarith)
    apply lt_of_le_of_lt _ hd
    exact div_le_div_of_nonneg_left hA.le hn0 (by
      simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1 ≤ 5 by omega))
  obtain ⟨t,p,U,hSupport,ht,hU,hbad,hsign⟩ := hdata s hsN
  refine ⟨t,p,U,hSupport,ht,hU,?_⟩
  intro S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog hb P _ ℓ q hq ν _ hv hregion
  let μ := Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  let Bad : Set (t → Fin 3 → ℂ) := {γ | (∃ i j, n < ‖γ i j‖) ∨ ∃ y ∈ E,
    ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
      (fun i j => U i j ∘ normalWaveEquiv) γ) y‖ < 1/n^110}
  have hBad : μ Bad ≤ ENNReal.ofReal (A/n^5) :=
    hbad S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog
  let V := ∑ a, q a*(ν a univ).toReal
  let F := fun γ => ∑ a, q a*∑ j : Fin 3, (ν a {x | finiteWaveSuperposition w U γ x *
    finiteWaveSuperposition w U γ (packetAxisShift x n ε (ℓ a) j) < 0}).toReal
  have hshift (a : P) (j : Fin 3) : Continuous (fun x => packetAxisShift x n ε (ℓ a) j) :=
    continuous_id.add continuous_const
  obtain ⟨hF,hFb,hFe⟩ := finite_regions_wave_sign_expectation w U hw.continuous
    (fun i j => (hU i j).1.continuous) (fun a j x => packetAxisShift x n ε (ℓ a) j) hshift ν q hq p₀ (by
      intro a
      filter_upwards [hregion a] with x hx
      exact hsign w hb x hx.1 (ℓ a) hx.2.1 hx.2.2.1 hx.2.2.2)
  have htBad : (μ Bad).toReal < p₀/6 := by
    apply lt_of_le_of_lt _ hAn
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ A/n^5)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hBad
  obtain ⟨γ,hγ,hscore⟩ := exists_large_score_avoiding μ F hF Bad
    (3*V) (p₀*V) ((p₀/2)*V)
    (fun γ => (hFb γ).2)
    (by positivity) hFe (by
      have hm := mul_lt_mul_of_pos_left htBad (show 0 < 3*V by dsimp [V]; positivity)
      nlinarith [mul_pos hp₀ hv])
  exact ⟨γ,(fun i j => le_of_not_gt (fun hh => hγ (Or.inl ⟨i,j,hh⟩))),
    (fun y hy => le_of_not_gt (fun hh => hγ (Or.inr ⟨y,hy,hh⟩))),hscore⟩
end


open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_waves_subregions_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ Q > 0,
    ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
    let n := s^4
    ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
    ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
      (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
      (t.card : ℝ) ≤ Q*n^3 ∧
      (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
        U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ max m 2,
          ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
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
        ∀ J : Set NormalWaveSpace, J ⊆ K →
        (∀ y ∈ J, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (P : Type) [Fintype P] (ℓ q : P → ℝ), (∀ a, 0 ≤ q a) →
        ∀ ν : P → Measure NormalWaveSpace, ∀ _ : ∀ a, IsFiniteMeasure (ν a),
        0 < ∑ a, q a*(ν a univ).toReal →
        (∀ a, ∀ᵐ x ∂ν a, x ∈ J ∧ profileFrequencyScale g φ x ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ x ∧ (∀ j, packetAxisShift x n ε (ℓ a) j ∈ J)) →
        ∃ γ : t → Fin 3 → ℂ, (∀ i j, ‖γ i j‖ ≤ n) ∧
          (∀ y ∈ E, 1/n^110 ≤
            ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
              (fun i j => U i j ∘ normalWaveEquiv) γ) y‖) ∧
          (p₀/2)*(∑ a, q a*(ν a univ).toReal) <
            ∑ a, q a*∑ j : Fin 3, (ν a {x | finiteWaveSuperposition w U γ x *
              finiteWaveSuperposition w U γ (packetAxisShift x n ε (ℓ a) j) < 0}).toReal := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := compact_actual_sign_noncancellation_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,T,hT,c,hc,A,hA,Q,hQ,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m D T₀ H hT₀ hH
  refine ⟨c₀,hc₀,T,hT,c,hc,Q,hQ,max N (12*A/p₀+1),le_max_of_le_left hN,?_⟩
  intro s hs
  have hsN : N ≤ s := (le_max_left _ _).trans hs
  have hs1 : 1 ≤ s := (by linarith : (1:ℝ) ≤ N).trans hsN
  have hs4 : s ≤ s^4 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1 ≤ 4 by omega)
  let n := s^4
  have hn1 : 1 ≤ n := hs1.trans hs4
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  have hAn : A/n^5 < p₀/6 := by
    have hlarge : 12*A/p₀ < n := (lt_add_one _).trans_le (((le_max_right _ _).trans hs).trans hs4)
    have hm := (div_lt_iff₀ hp₀).mp hlarge
    have hd : A/n < p₀/6 := (div_lt_iff₀ hn0).mpr (by nlinarith)
    apply lt_of_le_of_lt _ hd
    exact div_le_div_of_nonneg_left hA.le hn0 (by
      simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1 ≤ 5 by omega))
  obtain ⟨t,p,U,hSupport,ht,hU,hbad,hsign⟩ := hdata s hsN
  refine ⟨t,p,U,hSupport,ht,hU,?_⟩
  intro S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog J hJK hb P _ ℓ q hq ν _ hv hregion
  let μ := Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  let Bad : Set (t → Fin 3 → ℂ) := {γ | (∃ i j, n < ‖γ i j‖) ∨ ∃ y ∈ E,
    ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
      (fun i j => U i j ∘ normalWaveEquiv) γ) y‖ < 1/n^110}
  have hBad : μ Bad ≤ ENNReal.ofReal (A/n^5) :=
    hbad S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog
  let V := ∑ a, q a*(ν a univ).toReal
  let F := fun γ => ∑ a, q a*∑ j : Fin 3, (ν a {x | finiteWaveSuperposition w U γ x *
    finiteWaveSuperposition w U γ (packetAxisShift x n ε (ℓ a) j) < 0}).toReal
  have hshift (a : P) (j : Fin 3) : Continuous (fun x => packetAxisShift x n ε (ℓ a) j) :=
    continuous_id.add continuous_const
  obtain ⟨hF,hFb,hFe⟩ := finite_regions_wave_sign_expectation w U hw.continuous
    (fun i j => (hU i j).1.continuous) (fun a j x => packetAxisShift x n ε (ℓ a) j) hshift ν q hq p₀ (by
      intro a
      filter_upwards [hregion a] with x hx
      have hb' : ∀ y ∈ K, |(J.indicator w) y| ≤ c₀*Real.exp (n*φ y) := by
        intro y _
        by_cases hy : y ∈ J
        · simpa only [Set.indicator_of_mem hy] using hb y hy
        · simp only [Set.indicator_of_notMem hy, abs_zero]
          positivity
      obtain ⟨j,hj⟩ := hsign (J.indicator w) hb' x (hJK hx.1) (ℓ a)
        hx.2.1 hx.2.2.1 (fun j => hJK (hx.2.2.2 j))
      refine ⟨j,?_⟩
      simpa only [finiteWaveSuperposition, Set.indicator_of_mem hx.1,
        Set.indicator_of_mem (hx.2.2.2 j)] using hj)
  have htBad : (μ Bad).toReal < p₀/6 := by
    apply lt_of_le_of_lt _ hAn
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ A/n^5)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hBad
  obtain ⟨γ,hγ,hscore⟩ := exists_large_score_avoiding μ F hF Bad
    (3*V) (p₀*V) ((p₀/2)*V)
    (fun γ => (hFb γ).2)
    (by positivity) hFe (by
      have hm := mul_lt_mul_of_pos_left htBad (show 0 < 3*V by dsimp [V]; positivity)
      nlinarith [mul_pos hp₀ hv])
  exact ⟨γ,(fun i j => le_of_not_gt (fun hh => hγ (Or.inl ⟨i,j,hh⟩))),
    (fun y hy => le_of_not_gt (fun hh => hγ (Or.inr ⟨y,hy,hh⟩))),hscore⟩


end YauCounterexamples
end

end OAI
