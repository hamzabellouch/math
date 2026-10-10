import OAI.NumberTheory.CubicMoment.Angular.AngularHeightCoprimeDispersion
import OAI.NumberTheory.CubicMoment.Estimates.HeightGramContinuity

namespace OAI

/-! The actual full variance has the required averaged upper bound.
The shared-prime remainder is uniform in height and is retained. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_height_full_variance_saving
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hcop⟩ := angular_height_coprime_dispersion_saving ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k
  refine ⟨min η c,σ,lt_min hη hc,(min_le_left _ _).trans hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,L₁,m,hK₁,hcop⟩ := hcop L W hL hW hlo hhi
  have hηc : min η c/4 ≤ c := by linarith [min_le_right η c]
  obtain ⟨G,K₂,L₂,hK₂,hrem⟩ := angular_fullPrime_divisor_noncoprime_log_saving ℓ
    (η := min η c/4) hR hc hc₁ hηc hW hlo hhi V hV hV' k
  refine ⟨G,K₁+2*K₂,max L₁ L₂,m,by positivity,?_⟩
  intro r X A e u T hL₀ hprod hX hAlo hAhi he heN hT hThi hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos (zero_lt_one.trans_le hz) m).trans_le hT
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hA₂ : A ≤ (L r)^2 := hAhi.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hz))
  have hAcop : (L r)^(1-η/4) ≤ A :=
    (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [min_le_left η c])).trans hAlo
  have hX₁ : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hrough : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hX i)
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := angularHeightPrimeCoefficient ℓ R (W r) X
  have hS : ∀ a ∈ S, primary a := fun a ha => (fullSquarefreePrimeSupport_primary R (W r) X e ha).1
  let E := K₂*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k
  have hr (v : ℝ) : ‖smoothedDispersionVariance S β v V A-coprimeDispersionGram S β v V A‖ ≤ E := by
    have hh := hrem r X A 1 e v ((le_max_right L₁ L₂).trans hL₀) (hL r) hX₁ hprod hrough
      primary_one (by simpa only [norm_one_eq] using hL r) hAlo hAhi
    rwa [divisorDispersionVariance_one,divisorCoprimeDispersionGram_one _ hS] at hh
  have hvc : Continuous (fun t : ℝ => smoothedDispersionVariance S β (u+t) V A) := (continuous_smoothedDispersionVariance S hS β V hV hV' hA).comp
    (continuous_const.add continuous_id)
  have hcc : Continuous (fun t : ℝ => coprimeDispersionGram S β (u+t) V A) := (continuous_coprimeDispersionGram S β V A).comp (continuous_const.add continuous_id)
  have havg := dyadicHeightMean_mono (g := fun v => ‖coprimeDispersionGram S β (u+v) V A‖+E)
    hvc.norm (hcc.norm.add continuous_const) hTp (fun v _ => by
    have h := (norm_add_le
      (smoothedDispersionVariance S β (u+v) V A-coprimeDispersionGram S β (u+v) V A)
      (coprimeDispersionGram S β (u+v) V A)).trans (add_le_add (hr (u+v)) le_rfl)
    rw [sub_add_cancel] at h
    exact h.trans_eq (add_comm _ _))
  change dyadicHeightMean (fun v => ‖smoothedDispersionVariance S β (u+v) V A‖) T ≤
    dyadicHeightMean (fun v => ‖coprimeDispersionGram S β (u+v) V A‖+E) T at havg
  rw [dyadicHeightMean_add hcc.norm continuous_const,dyadicHeightMean_const _ hTp.ne'] at havg
  have hb := hcop r X A e u T ((le_max_left L₁ L₂).trans hL₀) hprod hX
    hAcop hA₂ he heN hT hThi hu
  apply havg.trans
  exact (add_le_add hb le_rfl).trans_eq (by dsimp [E]; ring)

end CubicFirstMoment

end

end OAI
