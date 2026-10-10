import OAI.NumberTheory.CubicMoment.Angular.AngularTypeIMixedFull
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularTypeIMixedPrime

namespace OAI

/-! Removing the auxiliary level dyad from the actual prime-convolution
mixed term. Only a fixed dilation of the product norm interval is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem angular_logarithmic_prime_typeI_mixed_full_actual
    {γ : Type*} {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {δ : Type*} {V : δ → ℝ → ℂ} (hVw : UniformLogWeights V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B R₀ : ℝ} (hB : 1 ≤ B) (J : ℕ) (hJ : R₀^Fintype.card ι < (2:ℝ)^J) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : γ) (Xi : ι → ℝ) (e : Eisenstein)
      (w : Eisenstein → δ) (t U : ℝ),
      1 ≤ L j → (∀ i, 0 < Xi i) → (∏ i, Xi i) = L j →
      (∀ i x, x < 1 → W j i x = 0) → (∀ i x, R₀ < x → W j i x = 0) →
      1 ≤ U → 2 ≤ L j*U → B ≤ L j*U → (2:ℝ)^J*L j ≤ (L j*U)^(51/100:ℝ) →
      (∀ r ∈ fullSquarefreePrimeSupport R₀ (W j) Xi e, ∀ x : ℝ, B < x → V (w r) x = 0) →
      let β := fun r => angularHeightPrimeCoefficient ℓ R₀ (W j) Xi r*normTwist t r
      ‖∑ r ∈ fullSquarefreePrimeSupport R₀ (W j) Xi e,
          β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ ≤
        K*U^(-1/6:ℝ)*(L j*U)^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := angular_logarithmic_prime_typeI_mixed_actual ℓ  hW hVw hGamma hB
  let C : ℝ := (2:ℝ)^J
  let p : ℝ := 5/6-1/100
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨(J:ℝ)*K*C^p,by positivity,?_⟩
  intro j Xi e w t U hL hXi hprod hlo hhi hU hX hBX hscale hcut
  let S := fullSquarefreePrimeSupport R₀ (W j) Xi e
  let β := fun r => angularHeightPrimeCoefficient ℓ R₀ (W j) Xi r*normTwist t r
  have hLp : 0 < L j := zero_lt_one.trans_le hL
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hXp : 0 < L j*U := mul_pos hLp hUp
  have hSn (r : Eisenstein) (hr : r ∈ S) :
      L j ≤ norm r ∧ norm r ≤ R₀^Fintype.card ι*L j := by
    simpa only [hprod] using fullPrimeProduct_norm_bounds R₀ (W j) Xi hXi hlo hhi
      (Finset.mem_filter.mp hr).1
  change ‖∑ r ∈ S, β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ ≤
    ((J:ℝ)*K*C^p)*U^(-1/6:ℝ)*(L j*U)^p
  rw [typeIMixedDyad_partition S hLp hJ hSn]
  calc
    _ ≤ ∑ i ∈ Finset.range J, ‖∑ r ∈ typeIMixedDyad S (L j) i,
        β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range J, K*U^(-1/6:ℝ)*(C*(L j*U))^p := by
      apply Finset.sum_le_sum
      intro i hi
      let R := L j*(2:ℝ)^i
      have hiJ : i ≤ J := (Finset.mem_range.mp hi).le
      have hpow : (2:ℝ)^i ≤ C := pow_le_pow_right₀ (by norm_num) hiJ
      have hLR : L j ≤ R := by
        dsimp [R]
        exact le_mul_of_one_le_right hLp.le (one_le_pow₀ (by norm_num))
      have hR : 1 ≤ R := hL.trans hLR
      have hRC : R ≤ C*L j := by
        dsimp [R]
        nlinarith [mul_le_mul_of_nonneg_left hpow hLp.le]
      have hXR : L j*U ≤ R*U := mul_le_mul_of_nonneg_right hLR hUp.le
      have hRX : R ≤ (R*U)^(51/100:ℝ) :=
        (hRC.trans hscale).trans (Real.rpow_le_rpow hXp.le hXR (by norm_num))
      have hlevels (r : Eisenstein) (hr : r ∈ typeIMixedDyad S (L j) i) :
          primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R := by
        have hm := Finset.mem_filter.mp hr
        have hn := typeIMixedDyadIndex_bounds hLp (hSn r hm.1).1
        rw [hm.2] at hn
        exact ⟨(fullSquarefreePrimeSupport_primary R₀ (W j) Xi e hm.1).1,hn.1,hn.2.le⟩
      have hb := hbound j Xi R₀ w (typeIMixedDyad S (L j) i) t (R*U) R U hL
        ((le_mul_of_one_le_right hLp.le hU).trans hXR) (hX.trans hXR) (hBX.trans hXR)
        hR hU rfl hRX hlevels (fun r hr => hcut r (Finset.mem_filter.mp hr).1)
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (Real.rpow_nonneg hUp.le _))
      apply Real.rpow_le_rpow (by positivity : 0 ≤ R*U) _ (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hRC hUp.le]
    _ = ((J:ℝ)*K*C^p)*U^(-1/6:ℝ)*(L j*U)^p := by
      rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Real.mul_rpow hC hXp.le]
      ring

end CubicFirstMoment

end

end OAI
