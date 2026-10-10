import Mathlib
import OAI.Geometry.SmoothYau.Limits.CompactActualMetricPackets
import OAI.Geometry.SmoothYau.Limits.CompactActualMetricPacketsSupported
import OAI.Geometry.SmoothYau.Limits.CompactMetricPacketSignGain

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
lemma gaussian_pi_uncurry_preserving (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (fun γ : I → J → ℂ => fun p : I×J => γ p.1 p.2)
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => stdGaussian ℂ)))
      (Measure.pi (fun _ : I×J => stdGaussian ℂ)) := by
  refine ⟨Measurable.of_eval (fun pair =>
    (measurable_pi_apply pair.2).comp (measurable_pi_apply pair.1)),?_⟩
  have h := Measure.infinitePi_map_curry_symm (fun (_ : I) (_ : J) => stdGaussian ℂ)
  simp only [Measure.infinitePi_eq_pi, MeasurableEquiv.coe_curry_symm] at h
  convert h using 1
  congr 1

lemma gaussian_flat_sign_eq {I : Type*} [Fintype I]
    (U : I → Fin 3 → ℂ) (V : I → Fin 3 → ℂ) (a b : ℝ) :
    (Measure.pi (fun _ : I×Fin 3 => stdGaussian ℂ))
      {γ | (a+complexGaussianRealValue (fun k => U k.1 k.2) γ)*
        (b+complexGaussianRealValue (fun k => V k.1 k.2) γ)<0} =
    (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {γ | (a+∑ i, ∑ ℓ, (γ i ℓ*U i ℓ).re)*(b+∑ i, ∑ ℓ, (γ i ℓ*V i ℓ).re)<0} := by
  classical
  have hm (Z : I×Fin 3 → ℂ) : Measurable (complexGaussianRealValue Z) := by
    unfold complexGaussianRealValue
    exact Finset.measurable_sum _ (fun i _ => Complex.measurable_re.comp ((measurable_pi_apply i).mul_const _))
  have hs : MeasurableSet {γ : I×Fin 3 → ℂ |
      (a+complexGaussianRealValue (fun k => U k.1 k.2) γ)*
        (b+complexGaussianRealValue (fun k => V k.1 k.2) γ)<0} :=
    measurableSet_lt ((measurable_const.add (hm _)).mul (measurable_const.add (hm _))) measurable_const
  rw [←(gaussian_pi_uncurry_preserving I (Fin 3)).measure_preimage hs.nullMeasurableSet]
  congr 1
  ext γ
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,complexGaussianRealValue,Fintype.sum_prod_type]
end



section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_waves_sign_and_jets
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ C > 0, ∃ Q > 0,
    ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
    let n := s^4
    ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
    ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
      (t.card : ℝ) ≤ Q*n^3 ∧
      (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
        U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
            (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
      (∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ y ∈ normalWaveEquiv.symm '' K,
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
        let W := Real.exp (n*φ (normalWaveEquiv y))+R
        ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
            (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
          ENNReal.ofReal (C*n^28*r^4)) ∧
      ∀ b : NormalWaveSpace → ℝ, (∀ y ∈ K, |b y| ≤ c₀*Real.exp (n*φ y)) →
      ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
      (∀ j, packetAxisShift x n ε ℓ j ∈ K) →
      ∃ j, ENNReal.ofReal p₀ ≤ (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition b U γ x *
          finiteWaveSuperposition b U γ (packetAxisShift x n ε ℓ j) < 0} := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hsign⟩ := compact_metric_packet_sign_gain g hK
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D
  obtain ⟨c₀,hc₀,hsg⟩ := hsign φ hφ
  obtain ⟨T,hT,c,hc,M,hM,C,hC,Q,hQ,rₑ,hrₑ,N₁,hN₁,hpack⟩ :=
    compact_actual_metric_packets g φ hφ hK hnc hcrit m D
  obtain ⟨N₂,hN₂,hsgn⟩ := hsg T c M rₑ (3*Q) hT hc hM hrₑ (by positivity)
  refine ⟨c₀,hc₀,T,hT,c,hc,C,hC,Q,hQ,max 2 (max N₁ N₂),le_max_left _ _,?_⟩
  intro s hs
  have hs2 : 2 ≤ s := (le_max_left _ _).trans hs
  have hsN₁ : N₁ ≤ s := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hs
  have hsN₂ : N₂ ≤ s := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hs
  have hs1 : 1 ≤ s := by linarith
  have hs4 : s ≤ s^4 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (by norm_num : 1 ≤ (4:ℕ))
  dsimp only
  obtain ⟨t,p,z,U,ht,hcover,hz,hU,hend,hjets⟩ := hpack (s^4) (hsN₁.trans hs4)
  refine ⟨t,p,U,ht,hU,hjets,?_⟩
  intro b hb x hx ℓ hℓ hℓ' hy
  have hcard : (Fintype.card (t×Fin 3) : ℝ) ≤ (3*Q)*(s^4)^3 := by
    simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [ht]
  obtain ⟨j,hj⟩ := hsgn s hsN₂ (t×Fin 3) (fun i => (p i.1).1)
    (fun i => z i.1 i.2) (fun i => U i.1 i.2) b hcard
    (fun i => (p i.1).property) (fun i => hz i.1 i.2) (by
      intro y hy
      obtain ⟨i,hi⟩ := hcover y hy
      exact ⟨(i,0),hi⟩)
    (fun i => (hU i.1 i.2).2.2.1) (by
      intro i y
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one]
        using ((hU i.1 i.2).2.2.2 y 0 (Nat.zero_le _)).1)
    (fun i => hend i.1 i.2) hb x hx ℓ hℓ hℓ' hy
  refine ⟨j,?_⟩
  rw [gaussian_flat_sign_eq (fun i ℓ => U i ℓ x)
    (fun i k => U i k (packetAxisShift x (s^4) ε ℓ j)) (b x)
    (b (packetAxisShift x (s^4) ε ℓ j))] at hj
  exact hj
end



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_waves_sign_and_jets_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ C > 0, ∃ Q > 0,
    ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
    let n := s^4
    ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
    ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
      (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
      (t.card : ℝ) ≤ Q*n^3 ∧
      (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
        U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
            (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
      (∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ y ∈ normalWaveEquiv.symm '' K,
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
        let W := Real.exp (n*φ (normalWaveEquiv y))+R
        ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
            (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
          ENNReal.ofReal (C*n^28*r^4)) ∧
      ∀ b : NormalWaveSpace → ℝ, (∀ y ∈ K, |b y| ≤ c₀*Real.exp (n*φ y)) →
      ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
      (∀ j, packetAxisShift x n ε ℓ j ∈ K) →
      ∃ j, ENNReal.ofReal p₀ ≤ (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition b U γ x *
          finiteWaveSuperposition b U γ (packetAxisShift x n ε ℓ j) < 0} := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hsign⟩ := compact_metric_packet_sign_gain g hK
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D
  obtain ⟨c₀,hc₀,hsg⟩ := hsign φ hφ
  obtain ⟨T,hT,c,hc,M,hM,C,hC,Q,hQ,rₑ,hrₑ,N₁,hN₁,hpack⟩ :=
    compact_actual_metric_packets_supported g φ hφ hK hO hKO hnc hcrit m D
  obtain ⟨N₂,hN₂,hsgn⟩ := hsg T c M rₑ (3*Q) hT hc hM hrₑ (by positivity)
  refine ⟨c₀,hc₀,T,hT,c,hc,C,hC,Q,hQ,max 2 (max N₁ N₂),le_max_left _ _,?_⟩
  intro s hs
  have hs2 : 2 ≤ s := (le_max_left _ _).trans hs
  have hsN₁ : N₁ ≤ s := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hs
  have hsN₂ : N₂ ≤ s := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hs
  have hs1 : 1 ≤ s := by linarith
  have hs4 : s ≤ s^4 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (by norm_num : 1 ≤ (4:ℕ))
  dsimp only
  obtain ⟨t,p,z,U,hSupport,ht,hcover,hz,hU,hend,hjets⟩ := hpack (s^4) (hsN₁.trans hs4)
  refine ⟨t,p,U,hSupport,ht,hU,hjets,?_⟩
  intro b hb x hx ℓ hℓ hℓ' hy
  have hcard : (Fintype.card (t×Fin 3) : ℝ) ≤ (3*Q)*(s^4)^3 := by
    simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [ht]
  obtain ⟨j,hj⟩ := hsgn s hsN₂ (t×Fin 3) (fun i => (p i.1).1)
    (fun i => z i.1 i.2) (fun i => U i.1 i.2) b hcard
    (fun i => (p i.1).property) (fun i => hz i.1 i.2) (by
      intro y hy
      obtain ⟨i,hi⟩ := hcover y hy
      exact ⟨(i,0),hi⟩)
    (fun i => (hU i.1 i.2).2.2.1) (by
      intro i y
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one]
        using ((hU i.1 i.2).2.2.2 y 0 (Nat.zero_le _)).1)
    (fun i => hend i.1 i.2) hb x hx ℓ hℓ hℓ' hy
  refine ⟨j,?_⟩
  rw [gaussian_flat_sign_eq (fun i ℓ => U i ℓ x)
    (fun i k => U i k (packetAxisShift x (s^4) ε ℓ j)) (b x)
    (b (packetAxisShift x (s^4) ε ℓ j))] at hj
  exact hj

end YauCounterexamples
end

end OAI
