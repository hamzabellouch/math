import OAI.NumberTheory.DirichletL.Descent.MarkedTwists

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*}

def markTwist (p : ι → Eis) (T : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ T, coprimalityMask (p i)

theorem markTwist_norm (p : ι → Eis) (T : Finset ι) (x : Eis) : ‖markTwist p T x‖ ≤ 1 := by
  simp only [markTwist, MonoidHom.finsetProd_apply, norm_prod]
  exact Finset.prod_le_one₀ (fun i hi => norm_nonneg _) (fun i hi => coprimalityMask_norm _ _)

theorem markTwist_periodic (p : ι → Eis) (S T : Finset ι) (hTS : T ⊆ S) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i ∈ S, p i}) (markTwist p T) := by
  intro x y hxy
  simp only [markTwist, MonoidHom.finsetProd_apply]
  apply Finset.prod_congr rfl
  intro i hi
  apply coprimalityMask_periodic (p i) x y
  apply Ideal.mem_span_singleton.mpr
  exact (Finset.dvd_prod_of_mem p (hTS hi)).trans (Ideal.mem_span_singleton.mp hxy)

def markedThetaQuotient (p : ι → Eis) (S : Finset ι) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) : ℂ :=
  fixedThetaQuotient Ψ c x * ∏ i ∈ S, if p i ∣ Quotient.out x then 1 else 0

theorem markedThetaQuotient_twists (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i)) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) :
    markedThetaQuotient p S Ψ c x =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * fixedThetaQuotient (markTwist p T * Ψ) c x := by
  have hmark (i : ι) (hi : i ∈ S) :
      (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
        1 - coprimalityMask (p i) (Quotient.out x) := by
    change (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
      1 - (if IsCoprime (p i) (Quotient.out x) then 1 else 0)
    rw [(hp i hi).coprime_iff_not_dvd]
    by_cases h : p i ∣ Quotient.out x <;> simp [h]
  unfold markedThetaQuotient
  rw [Finset.prod_congr rfl hmark, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [show markTwist p T * Ψ = Ψ * markTwist p T from mul_comm _ _]
  simp only [fixedThetaQuotient, fixedThetaTwist_mul, markTwist, MonoidHom.finsetProd_apply]
  ring

theorem markedCompletedT_canonical_reflection (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (hΨ : ∀ x, ‖Ψ x‖ ≤ 1)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (v0 v1 : ℝ) (hv0 : 0 < v0) (hWs : Function.support W ⊆ Set.Icc v0 v1)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Ψ c) h *
          (finiteTwistCusp c hc h).smoothedKernel W X := by
  have hnorm (T : Finset ι) : ∀ x, ‖(markTwist p T * Ψ) x‖ ≤ 1 := by
    intro x
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_mul_of_nonneg_right (markTwist_norm p T x) (norm_nonneg _)).trans
      ((one_mul _).le.trans (hΨ x))
  have hper (T : Finset ι) (hT : T ∈ S.powerset) :
      CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i ∈ S, p i})
        (markTwist p T * Ψ) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [markTwist_periodic p S T (Finset.mem_powerset.mp hT) x y (Ideal.mul_le_right hxy),
      hperiod x y (Ideal.mul_le_left hxy)]
  have hcoeff (h : Eis ⧸ Ideal.span {c}) :
      finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Ψ c) h =
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          finiteAdditiveFourierCoeff (quotientTrace c hc)
            (fixedThetaQuotient (markTwist p T * Ψ) c) h := by
    unfold finiteAdditiveFourierCoeff
    simp_rw [markedThetaQuotient_twists p S hp Ψ c]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]
  rw [markedCompletedT_prime_product_twists S p hp Ψ W hWcompact X hX]
  change (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * completedT (markTwist p T * Ψ) W X) = _
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (thetaDerivativeScalar⁻¹ *
        ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc)
          (fixedThetaQuotient (markTwist p T * Ψ) c) h *
            (finiteTwistCusp c hc h).smoothedKernel W X) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [completedT_canonical_smoothed_reflection _ (hnorm T) _ (hper T hT)
        c hc hcQ W v0 v1 hv0 hWs hW X hX]
    _ = _ := by
      simp_rw [hcoeff]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro T hT
      ring

end
end SevenEighths.InverseMoment

end OAI
