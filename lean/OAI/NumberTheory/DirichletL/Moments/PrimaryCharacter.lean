import OAI.NumberTheory.DirichletL.Moments.FixedRay

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentPrimaryCharacter
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimary CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def rawPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ where
  toFun n := primaryIdealCharacter r χ (Ideal.span {n})
  map_one' := by simp [← Ideal.one_eq_top]
  map_mul' x y := by rw [← Ideal.span_singleton_mul_span_singleton,map_mul]

def maskedPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ :=
  coprimalityMask (3:O)*rawPrimaryHom r χ

theorem maskedPrimaryHom_unit_mul (r : O) (χ : MulChar (Residue r) ℂ) (u : Oˣ) (n : O) :
    maskedPrimaryHom r χ ((u:O)*n)=maskedPrimaryHom r χ n := by
  change (if IsCoprime (3:O) ((u:O)*n) then (1:ℂ) else 0)*
      primaryIdealCharacter r χ (Ideal.span {(u:O)*n}) =
    (if IsCoprime (3:O) n then (1:ℂ) else 0)*primaryIdealCharacter r χ (Ideal.span {n})
  rw [isCoprime_mul_unit_left_right u.isUnit,Ideal.span_singleton_mul_left_unit u.isUnit]

theorem maskedPrimaryHom_ramified (r : O) (χ : MulChar (Residue r) ℂ) (n : O) (hn : λ₀∣n) :
    maskedPrimaryHom r χ n=0 := by
  have h3 : λ₀∣(3:O) := (dvd_pow_self λ₀ (by decide : 2≠0)).trans ActualEisensteinCubic.lambda_sq_dvd_three
  have hc : ¬IsCoprime (3:O) n := fun hc =>
    PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (hc.isUnit_of_dvd' h3 hn)
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*_=0
  rw [ite_eq_right hc,zero_mul]

theorem maskedPrimaryHom_primary (r : O) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : maskedPrimaryHom r χ n=χ (Ideal.Quotient.mk _ n) := by
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*
    χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {n})))=_
  rw [ite_eq_left (CubicEisenstein.primary_coprime_three n hn).symm,one_mul,
    CompletedGauss.primaryGenerator_span n (CubicJacobiGlobal.primary_ne_zero n hn) hn]

theorem maskedPrimaryHom_periodic (r : O) (χ : MulChar (Residue r) ℂ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {3*r}) (maskedPrimaryHom r χ) := by
  let F : O →* ℂ := χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom
  apply periodic_of_primary _ _ _ F _ (maskedPrimaryHom_unit_mul r χ)
    (maskedPrimaryHom_ramified r χ) (maskedPrimaryHom_primary r χ)
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact ActualEisensteinCubic.lambda_sq_dvd_three.trans (dvd_mul_right _ _)
  · intro x y hxy
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_left r 3).trans (Ideal.mem_span_singleton.mp hxy))

def primaryCharacter (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) : Character :=
  rowCharacter (Ideal.span {3*r})
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hr))
    (maskedPrimaryHom r χ) (maskedPrimaryHom_periodic r χ)
    (fun u => by simpa only [mul_one,map_one] using maskedPrimaryHom_unit_mul r χ u 1)

@[simp] theorem primaryCharacter_modulus (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus=Ideal.span {3*r} := rfl

theorem primaryCharacter_primary (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : elementCoeff (primaryCharacter r hr χ) n=χ (Ideal.Quotient.mk _ n) := by
  rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_primary r χ n hn]
  split_ifs with hc
  · rfl
  · symm
    apply MulChar.map_nonunit
    intro hu
    apply hc
    apply isUnit_residue_of_coprime
    apply (CubicEisenstein.primary_coprime_three n hn).symm.mul_left
    exact (CubicEisenstein.isUnit_quotient_span_iff r n).mp hu

theorem primaryCharacter_all (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O) :
    elementCoeff (primaryCharacter r hr χ) n=maskedPrimaryHom r χ n := by
  by_cases hn : λ₀∣n
  · rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_ramified r χ n hn]
    split_ifs <;> rfl
  · have hg := (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n).mpr hn
    have hs := CompletedGauss.primaryGenerator_spec (Ideal.span {n}) hg
    obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1.symm
    have hp : λ₀^2∣(u:O)*n-1 := by
      have hp' : λ₀^2∣CompletedGauss.primaryGenerator (Ideal.span {n})-1 := hs.2
      rwa [mul_comm,hu]
    rw [← elementCoeff_unit_mul (primaryCharacter r hr χ) u n,
      ← maskedPrimaryHom_unit_mul r χ u n,primaryCharacter_primary r hr χ _ hp,
      maskedPrimaryHom_primary r χ _ hp]

theorem primaryCharacter_ideal (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (primaryCharacter r hr χ) I=
      χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator I)) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  calc
    _ = elementCoeff (primaryCharacter r hr χ) (CompletedGauss.primaryGenerator I) := by
      rw [← idealCoeff_span _ hn,hs.1]
    _ = _ := primaryCharacter_primary r hr χ _ hs.2

theorem primaryCharacter_modulus_norm (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus.absNorm=
      (Ideal.span {(3:O)}).absNorm*(Ideal.span {r}).absNorm := by
  rw [primaryCharacter_modulus,← Ideal.span_singleton_mul_span_singleton,map_mul]

end SevenEighths.CenteredMomentPrimaryCharacter

end

end OAI
