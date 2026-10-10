import OAI.NumberTheory.CubicMoment.Angular.AngularHeightPoissonTail
import OAI.NumberTheory.CubicMoment.Angular.AngularHeightPoissonDyadic
import OAI.NumberTheory.CubicMoment.Estimates.HighPoissonLogSaving

namespace OAI

/-! The complete nonzero Poisson frequency series has an averaged
logarithmic saving. Its infinite tail is controlled uniformly in height. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_height_poisson_total_saving
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
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (H : ℕ → Finset Eisenstein)
        (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → (∀ j, H j ⊆ frequencyDyad j) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      dyadicHeightMean (fun t => ‖∑' j : ℕ,
        finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e) (H j)
          (angularHeightPrimeCoefficient ℓ R (W r) X) (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hshort⟩ := angular_height_poisson_dyadic_saving ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,L₁,m,hK₁,hshort⟩ := hshort L W hL hW hlo hhi
  obtain ⟨K₂,L₂,hK₂,htail⟩ := angular_high_poisson_log_saving ℓ hR hη hη₁ hW hlo hhi V hV hV' k
  obtain ⟨L₃,hL₃⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < η/2 by positivity)).eventually_ge_atTop 2)
  obtain ⟨K₀,a,_hK₀,henv⟩ := angular_logarithmic_absolute_poisson_dyad ℓ hR hW hlo hhi V hV hV' 3
  refine ⟨K₁+2*K₂,max L₁ (max L₂ L₃),m,by positivity,?_⟩
  intro r X A H e u T hL₀ hprod hX hAlo hAhi hH he heN hT hThi hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hA₁ : 1 ≤ A := (Real.one_le_rpow (hL r) (by linarith)).trans hAlo
  have hA : 0 < A := zero_lt_one.trans_le hA₁
  have hX₁ : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hL₁ := (le_max_left L₁ (max L₂ L₃)).trans hL₀
  have hL₂ := (le_max_left L₂ L₃).trans ((le_max_right L₁ (max L₂ L₃)).trans hL₀)
  have hL₃' := (le_max_right L₂ L₃).trans ((le_max_right L₁ (max L₂ L₃)).trans hL₀)
  obtain ⟨n,hn,hprefix⟩ := poisson_cutoff_exists (hL r) hη.le (hL₃ (L r) hL₃')
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := angularHeightPrimeCoefficient ℓ R (W r) X
  let F := fun j v => finitePoissonContribution S (H j) β (u+v) V A
  have hfc (j : ℕ) : Continuous (F j) :=
    (finitePoissonContribution_continuous_height S (H j) β V A).comp (continuous_const.add continuous_id)
  let t := A/(27*(R^Fintype.card ι*L r)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have htotal : Continuous (fun v => ∑' j : ℕ, F j v) :=
    continuous_poisson_series S H β V A u (C := K₀*A*L r*(1+Real.log (L r))^a) ht (fun j v => by
      have hh := henv r X (hL r) hX₁ hprod A e (u+v) j (H j) hA (hH j)
      convert hh using 1
      dsimp [t]
      ring)
  have hpre := hshort r X A (Finset.range n) H e u T hL₁ hprod hX hA
    (fun j hj => hprefix j (Finset.mem_range.mp hj)) hH he heN hT hThi hu
  have hpoint (v : ℝ) : ‖∑' j : ℕ, F j v‖ ≤
      ‖∑ j ∈ Finset.range n, F j v‖+K₂/(1+Real.log (L r))^k := by
    obtain ⟨hfs,hft⟩ := htail r X hL₂ (hL r) hX₁ hprod A e (u+v) n H hAlo hAhi hn hH
    exact norm_tsum_prefix_tail n hfs le_rfl hft
  have hsumc := continuous_finsetSum (Finset.range n) (fun j _ => hfc j)
  have hm := dyadicHeightMean_mono htotal.norm (hsumc.norm.add continuous_const) hTp
    (fun v _ => hpoint v)
  change dyadicHeightMean (fun v => ‖∑' j : ℕ, F j v‖) T ≤
    dyadicHeightMean (fun v => ‖∑ j ∈ Finset.range n, F j v‖+K₂/(1+Real.log (L r))^k) T at hm
  rw [dyadicHeightMean_add hsumc.norm continuous_const,dyadicHeightMean_const _ hTp.ne'] at hm
  have hscale : 1 ≤ A^(2/3:ℝ)*(L r)^(5/3:ℝ) := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hA₁ (by norm_num)) (Real.one_le_rpow (hL r) (by norm_num))
  apply hm.trans
  calc
    _ ≤ K₁*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k+
        2*(K₂/(1+Real.log (L r))^k) := add_le_add hpre le_rfl
    _ ≤ K₁*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k+
        2*(K₂*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))/(1+Real.log (L r))^k) := by
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hK₂.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
