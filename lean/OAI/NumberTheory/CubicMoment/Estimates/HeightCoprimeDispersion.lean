import OAI.NumberTheory.CubicMoment.Estimates.CoprimePoissonSeries

namespace OAI

/-! The averaged estimate for the original coprime Gram form, obtained
from the complete Poisson series without omitting any frequencies. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem height_coprime_dispersion_saving
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      dyadicHeightMean (fun t =>
        ‖coprimeDispersionGram (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hseries⟩ := height_poisson_total_saving
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K,L₀,m,hK,hseries⟩ := hseries L W hL hW hlo hhi
  refine ⟨K,max L₀ 2,m,hK,?_⟩
  intro r X A e u T hL₀ hprod hX hAlo hAhi he heN hT hThi hu
  have hL₂ : 2 ≤ L r := (le_max_right L₀ 2).trans hL₀
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hXpos : ∀ i, 0 < X i := fun i =>
    (Real.rpow_pos_of_pos (by linarith : 0 < 2*L r) c).trans (hX i)
  have hS : ∀ a ∈ fullSquarefreePrimeSupport R (W r) X e,
      primary a ∧ Squarefree a ∧ a ≠ 1 := by
    intro a ha
    refine ⟨(fullSquarefreePrimeSupport_primary R (W r) X e ha).1,
      (fullSquarefreePrimeSupport_primary R (W r) X e ha).2,?_⟩
    have hn := (fullPrimeProduct_norm_bounds R (W r) X hXpos (hlo r) (hhi r)
      (Finset.mem_filter.mp ha).1).1
    rw [hprod] at hn
    intro h
    rw [h,norm_one_eq] at hn
    linarith
  have hident (t : ℝ) := coprimeDispersionGram_eq_poisson_series _ hS
    (fullPrimeCoefficient R (W r) X) (u+t) V hV hV' hA
  simp_rw [hident]
  exact hseries r X A frequencyDyad e u T ((le_max_left L₀ 2).trans hL₀)
    hprod hX hAlo hAhi (fun _ => Finset.Subset.refl _) he heN hT hThi hu

end CubicFirstMoment

end

end OAI
