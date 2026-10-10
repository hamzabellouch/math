import OAI.NumberTheory.CubicMoment.Estimates.DivisorNoncubeTotal
import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorNoncubeDyadic
import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorHighSaving

namespace OAI

/-! All effective noncube frequencies of each small square divisor.
The finite annuli and the infinite Fourier tail are both retained. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_divisor_noncube_total_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (d e : Eisenstein) (u : ℝ) (hd : d ≠ 0), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) → norm d ≤ (L r)^(η/16) →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2 →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖divisorNoncubePoissonContribution d hd (fullSquarefreePrimeSupport R (W r) X e)
        (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hshort⟩ := angular_divisor_noncube_dyadic_saving ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k U
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,T₁,hK₁,hshort⟩ := hshort L W hL hW hlo hhi
  obtain ⟨K₂,T₂,hK₂,htail⟩ := angular_divisor_high_poisson_log_saving ℓ hR hη hη₁ hW hlo hhi V hV hV' k
  obtain ⟨T₃,hT₃⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < η/2 by positivity)).eventually_ge_atTop 2)
  refine ⟨K₁+K₂,max T₁ (max T₂ T₃),by positivity,?_⟩
  intro r X A d e u hd hT hprod hX hdhi hAlo hAhi he heN hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hd1 : 1 ≤ norm d := one_le_norm hd
  have hA₁ : 1 ≤ A := (Real.one_le_rpow (hL r) (by linarith)).trans hAlo
  have hA : 0 < A := zero_lt_one.trans_le hA₁
  have hX₁ : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hT₁ := (le_max_left T₁ (max T₂ T₃)).trans hT
  have hT₂ := (le_max_left T₂ T₃).trans ((le_max_right T₁ (max T₂ T₃)).trans hT)
  have hT₃' := (le_max_right T₂ T₃).trans ((le_max_right T₁ (max T₂ T₃)).trans hT)
  obtain ⟨n,hn,hprefix⟩ := poisson_cutoff_exists (hL r) hη.le (hT₃ (L r) hT₃')
  let H := fun j => (divisorFrequencyDyad d hd j).filter (fun h => ¬∃ z : Eisenstein, z^3 = d*h)
  let F := fun j => finiteDivisorPoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
    (H j) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A
  have hs := hshort r X A (Finset.range n) H d e u hT₁ hprod hX hA hd
    (fun j hj => hprefix j (Finset.mem_range.mp hj))
    (fun j _ h hh => ⟨mem_divisorFrequencyDyad.mp (Finset.mem_filter.mp hh).1,
      (Finset.mem_filter.mp hh).2⟩) he heN hu
  obtain ⟨hfs,hft⟩ := htail r X hT₂ (hL r) hX₁ hprod A d e u n H hd hdhi hAlo hAhi hn
    (fun _ => Finset.filter_subset _ _)
  have hf : Summable (fun j : ℕ => F (j+n)) := hfs
  have hs' : ‖∑ j ∈ Finset.range n, F j‖ ≤
      K₁*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
    apply hs.trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact le_mul_of_one_le_left (pow_nonneg hz.le _) hd1
  have ht' : ‖∑' j : ℕ, F (j+n)‖ ≤ K₂/(1+Real.log (L r))^k := hft
  have hscale : 1 ≤ A^(2/3:ℝ)*(L r)^(5/3:ℝ) := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hA₁ (by norm_num)) (Real.one_le_rpow (hL r) (by norm_num))
  change ‖∑' j : ℕ, F j‖ ≤ _
  apply (norm_tsum_prefix_tail n hf hs' ht').trans
  calc
    _ ≤ K₁*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k+
        K₂*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))/(1+Real.log (L r))^k := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hK₂.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
