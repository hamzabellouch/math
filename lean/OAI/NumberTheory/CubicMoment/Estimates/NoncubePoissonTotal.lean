import OAI.NumberTheory.CubicMoment.Estimates.NoncubePoissonDyadic
import OAI.NumberTheory.CubicMoment.Estimates.HighPoissonLogSaving

namespace OAI

/-! Full noncube Poisson contribution: the bounded-conductor proof and
the actual infinite high-frequency tail give the full contribution. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def noncubePoissonContribution (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' j : ℕ, finitePoissonContribution S
    ((frequencyDyad j).filter (fun h => ¬∃ z : Eisenstein, z^3 = h)) β u V A

theorem noncube_poisson_total_saving (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖noncubePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
        (fullPrimeCoefficient R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hshort⟩ := noncube_poisson_dyadic_saving
    (γ := γ) (ι := ι) hSW hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k U
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,T₁,hK₁,hshort⟩ := hshort L W hL hW hlo hhi
  obtain ⟨K₂,T₂,hK₂,htail⟩ := high_poisson_log_saving hR hη hη₁ hW hlo hhi V hV hV' k
  obtain ⟨T₃,hT₃⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < η/2 by positivity)).eventually_ge_atTop 2)
  refine ⟨K₁+K₂,max T₁ (max T₂ T₃),by positivity,?_⟩
  intro r X A e u hT hprod hX hAlo hAhi he heN hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hA₁ : 1 ≤ A := (Real.one_le_rpow (hL r) (by linarith)).trans hAlo
  have hA : 0 < A := zero_lt_one.trans_le hA₁
  have hX₁ : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hT₁ := (le_max_left T₁ (max T₂ T₃)).trans hT
  have hT₂ := (le_max_left T₂ T₃).trans ((le_max_right T₁ (max T₂ T₃)).trans hT)
  have hT₃' := (le_max_right T₂ T₃).trans ((le_max_right T₁ (max T₂ T₃)).trans hT)
  obtain ⟨n,hn,hprefix⟩ := poisson_cutoff_exists (hL r) hη.le (hT₃ (L r) hT₃')
  let H := fun j => (frequencyDyad j).filter (fun h => ¬∃ z : Eisenstein, z^3 = h)
  let F := fun j => finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
    (H j) (fullPrimeCoefficient R (W r) X) u V A
  have hs := hshort r X A (Finset.range n) e u hT₁ hprod hX hA
    (fun j hj => hprefix j (Finset.mem_range.mp hj)) he heN hu
  obtain ⟨hfs,hft⟩ := htail r X hT₂ (hL r) hX₁ hprod A e u n H hAlo hAhi hn
    (fun j => Finset.filter_subset _ _)
  have hf : Summable (fun j : ℕ => F (j+n)) := hfs
  have hs' : ‖∑ j ∈ Finset.range n, F j‖ ≤
      K₁*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := hs
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
