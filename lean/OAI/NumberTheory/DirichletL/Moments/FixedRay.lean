import OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation
import OAI.NumberTheory.DirichletL.Moments.Primary
import OAI.NumberTheory.DirichletL.Hecke.RowClosure

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open RayFourExpansion CenteredMomentPrimary HeckeFamily HeckeRowClosure
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem supported_coprime_four (a : O) (ha : Supported (Ideal.span {a})) :
    IsCoprime (4 : O) a := by
  have hn := (supported_span_iff a).mp ha |>.2
  have hneg : IsCoprime (-2 : O) a :=
    CanonicalRowCompletion.negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
      (by simpa only [neg_dvd] using hn)
  have h2 : IsCoprime (2 : O) a := hneg.of_isCoprime_of_dvd_left ⟨-1, by ring⟩
  have h4 : IsCoprime ((2 : O)^2) a := h2.pow_left
  simpa only [show (2 : O)^2 = 4 by norm_num] using h4

theorem supported_coprime_twelve (a : O) (ha : Supported (Ideal.span {a})) :
    IsCoprime (12 : O) a := by
  have h9 := ShortDraftCRT.nine_coprime_of_not_lambda_dvd a ((supported_span_iff a).mp ha).1
  have h36 : IsCoprime (36 : O) a := by
    convert (supported_coprime_four a ha).mul_left h9 using 1 ; norm_num
  exact h36.of_isCoprime_of_dvd_left ⟨3, by norm_num⟩

theorem supported_rayMask (a : O) (ha : Supported (Ideal.span {a})) : rayMask a = 1 := by
  rw [rayMask, ite_eq_left (CenteredMomentCommonSupport.isUnit_residue_of_coprime
    4 a (supported_coprime_four a ha))]

def phaseTable (D E : O) (r s : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign
    (QuadraticGaussRay.residueQuotientFour r) (ActualEisensteinCoordinates.residue E) : ℂ) *
  (QuadraticAllOddCRT.quadraticRaySign
    (QuadraticGaussRay.residueQuotientFour s) (ActualEisensteinCoordinates.residue D) : ℂ) *
  (QuadraticAllOddCRT.quadraticRaySign
    (QuadraticGaussRay.residueQuotientFour r) (QuadraticGaussRay.residueQuotientFour s) : ℂ)

theorem phaseTable_mk (D E a b : O) :
    phaseTable D E (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) =
      sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b := by
  simp only [phaseTable, QuadraticGaussRay.residueQuotientFour_mk,
    sexticReciprocityPhase, star_intCast]

theorem phaseTable_norm (D E : O) (r s : RayRing) : ‖phaseTable D E r s‖ ≤ 1 := by
  unfold phaseTable QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> norm_num

theorem phaseTable_expansion (D E a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable D E) χ ξ * rayCharacter χ a * rayCharacter ξ b := by
  have h := pair_phase_expansion (phaseTable D E) a b
  simpa only [supported_rayMask a ha, supported_rayMask b hb, one_mul,
    phaseTable_mk] using h

theorem phaseTable_mass (D E : O) :
    (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖) ≤ 256 := by
  simpa only [mul_one] using pairCoeff_sum_norm_le (phaseTable D E) 1
    (fun u v => phaseTable_norm D E u v)

def primaryRayHom (χ : RayCharacter) : O →* ℂ where
  toFun n := primaryIdealCharacter 4 χ (Ideal.span {n})
  map_one' := by simp [← Ideal.one_eq_top]
  map_mul' x y := by rw [← Ideal.span_singleton_mul_span_singleton, map_mul]

theorem primaryRayHom_primary (χ : RayCharacter) (a : O) (hp : λ₀^2 ∣ a - 1) :
    primaryRayHom χ a = rayCharacter χ a := by
  change χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {a}))) = _
  rw [CompletedGauss.primaryGenerator_span a (CubicJacobiGlobal.primary_ne_zero a hp) hp]
  rfl

theorem primaryRayHom_unit_mul (χ : RayCharacter) (u : Oˣ) (a : O) :
    primaryRayHom χ ((u : O) * a) = primaryRayHom χ a := by
  change primaryIdealCharacter 4 χ (Ideal.span {(u : O) * a}) = _
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  rfl

theorem primaryRayHom_periodic (χ : RayCharacter) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(12 : O)}) (primaryRayHom χ) := by
  let F : O →* ℂ := χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {(4 : O)})).toMonoidHom
  refine periodic_of_primary _ ?_ _ F ?_ (primaryRayHom_unit_mul χ) ?_ ?_
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact ActualEisensteinCubic.lambda_sq_dvd_three.trans ⟨4, by norm_num⟩
  · intro x y hxy
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact (show (4 : O) ∣ 12 from ⟨3, by norm_num⟩).trans (Ideal.mem_span_singleton.mp hxy)
  · intro x hx
    have hz : CompletedGauss.primaryGenerator (Ideal.span {x}) = 0 := by
      by_contra hn
      exact (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff x).mp hn hx
    change χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {x}))) = 0
    let : Nontrivial RayRing := Fintype.one_lt_card_iff_nontrivial.mp (by rw [rayRing_card]; norm_num)
    rw [hz, map_zero, MulChar.map_zero]
  · exact primaryRayHom_primary χ

def primaryRayCharacter (χ : RayCharacter) : Character :=
  rowCharacter (Ideal.span {(12 : O)}) (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
    (primaryRayHom χ) (primaryRayHom_periodic χ) (by
      intro u
      simpa using primaryRayHom_unit_mul χ u 1)

@[simp] theorem primaryRayCharacter_modulus (χ : RayCharacter) :
    (primaryRayCharacter χ).modulus = Ideal.span {(12 : O)} := rfl

theorem primaryRayCharacter_primary (χ : RayCharacter) (a : O)
    (ha : Supported (Ideal.span {a})) (hp : λ₀^2 ∣ a - 1) :
    elementCoeff (primaryRayCharacter χ) a = rayCharacter χ a := by
  rw [primaryRayCharacter, elementCoeff_rowCharacter,
    ite_eq_left (CenteredMomentCommonSupport.isUnit_residue_of_coprime
      12 a (supported_coprime_twelve a ha)), primaryRayHom_primary χ a hp]

theorem completeSupportExtension_separated (D E h a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    completeSupportExtension D E hD hE h a b =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            (rayCharacter χ a * idealRowHom h (Ideal.span {a})) *
            (rayCharacter ξ b * star (idealRowHom (-h) (Ideal.span {b}))) := by
  rw [completeSupportExtension]
  have he := phaseTable_expansion D E a b ha hb
  calc
    _ = actualCorrelation D E hD hE h *
        (sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
          sexticReciprocityPhase a b) *
        idealRowHom h (Ideal.span {a}) * star (idealRowHom (-h) (Ideal.span {b})) := by ring
    _ = _ := by
      rw [he]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring

end SevenEighths.CenteredMomentFixedRay

end

end OAI
