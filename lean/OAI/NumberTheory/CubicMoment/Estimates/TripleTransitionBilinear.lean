import OAI.NumberTheory.CubicMoment.Estimates.PrimeTransitionBilinear

namespace OAI

/-! Insert the actual two-prime coefficient in the transition bound.
Its outer energy is proved from the PNT, not assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem two_prime_transition_bilinear {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hc : 0 < c)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
      T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      (∏ i, XA i) = A → (∀ i, (L r)^c ≤ XA i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) →
      let P := fullSquarefreePrimeSupport 2 WA XA 1
      let α := fullPrimeCoefficient 2 WA XA
      let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
      let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
      ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist u (a*b)‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
  obtain ⟨M,hM,hmass⟩ := fullPrimeCoefficient_power_scale_moments (ι := ι) hpnt
    (R := 2) (by norm_num) hc
  obtain ⟨Tm,hmass⟩ := eventually_atTop.mp hmass
  obtain ⟨η,K,T,hη,hη1,hK,hbound⟩ := single_prime_transition_bilinear hpnt hSW hpub
    hHuxley hperiod hMV hC (by norm_num : (1:ℝ) ≤ 4) hM.le hGI hGQ
    L W hL hW hlo hhi hW1 U
  refine ⟨η,K,max T Tm,hη,hη1,hK,?_⟩
  intro r A u WA XA hT hrough hAlo hAhi hu hprod hXA hAlow hAhigh hWA
  dsimp only
  let P := fullSquarefreePrimeSupport 2 WA XA 1
  let α := fullPrimeCoefficient 2 WA XA
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hXi (i : ι) : 0 < XA i := (Real.rpow_pos_of_pos hB c).trans_le (hXA i)
  have hP (a : Eisenstein) (ha : a ∈ P) : primary a ∧ norm a/A ∈ Set.Icc 1 4 := by
    have hp := fullSquarefreePrimeSupport_primary 2 WA XA 1 ha
    have hn := fullPrimeProduct_norm_bounds 2 WA XA hXi hAlow hAhigh
      (Finset.mem_filter.mp ha).1
    rw [hprod,hcard] at hn
    refine ⟨hp.1,(le_div_iff₀ hA).mpr (by simpa using hn.1),?_⟩
    apply (div_le_iff₀ hA).mpr
    norm_num at hn
    exact hn.2
  have hm := (hmass (L r) ((le_max_right _ _).trans hT) WA XA hXA hWA 1).2
  rw [hprod,hcard] at hm
  exact hbound r A u P α ((le_max_left _ _).trans hT) hrough hAlo hAhi hu hP hm

end CubicFirstMoment

end

end OAI
