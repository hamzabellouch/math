import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows
import OAI.NumberTheory.DirichletL.CenteredExceptionalCount
import OAI.NumberTheory.DirichletL.Detector.HighAbsolute

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ActualEisensteinCubic HeckeInverseAmplification CenteredExceptionalCount ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem sixthRow_surjective (H : NonzeroFrequency) :
    ∃p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,rowMap p=H.val := by
  let I : Id := Ideal.span {H.val}
  have hI : I≠0 := Ideal.span_singleton_eq_bot.not.mpr H.property
  let J : Id := sixthQuotient I
  have hJ : J≠0 := sixthQuotient_ne_zero I
  let a := idealGenerator J
  have ha : a≠0 := idealGenerator_ne_zero J hJ
  have hspan : Ideal.span {a}=J := span_idealGenerator J
  have hd : a^6∣H.val := by
    apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
    rw [←Ideal.span_singleton_pow,hspan]
    change J^6∣I
    rw [←sixth_normal_form I hI]
    exact dvd_mul_left _ _
  obtain ⟨u,hu⟩ := hd
  have hu0 : u≠0 := by
    intro hz
    rw [hz,mul_zero] at hu
    exact H.property hu
  have hsu : Ideal.span {u}=sixthRemainder I := by
    have hi : Ideal.span {u}*J^6=I := by
      rw [←hspan,Ideal.span_singleton_pow,Ideal.span_singleton_mul_span_singleton]
      exact congrArg (fun b : O=>Ideal.span {b}) (by simpa only [mul_comm] using hu.symm)
    apply mul_right_cancel₀ (pow_ne_zero 6 hJ)
    exact hi.trans (sixth_normal_form I hI).symm
  have hf : SixthFree (Ideal.span {u}) := by
    rw [hsu]
    intro P
    exact sixthRemainder_valuation_lt I P
  refine ⟨(⟨u,hu0,hf⟩,⟨J,hJ⟩),?_⟩
  change u*a^6=H.val
  simpa only [mul_comm] using hu.symm

def sixthFrequencyEquiv : FreeRow×HeckeInverseAmplification.NonzeroIdeal ≃ NonzeroFrequency :=
  Equiv.ofBijective (fun p=>⟨rowMap p,rowMap_ne_zero p⟩) ⟨
    fun p q h=>rowMap_injective (congrArg Subtype.val h),
    fun H=>by obtain ⟨p,hp⟩ := sixthRow_surjective H;exact ⟨p,Subtype.ext hp⟩⟩

lemma sixthFrequencyEquiv_apply (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) :
    (sixthFrequencyEquiv p).val=p.1.val*(idealGenerator p.2.val)^6 := rfl

theorem tsum_sixth_decomposition (f : NonzeroFrequency→ℂ) :
    (∑'H : NonzeroFrequency,f H)=
      ∑'p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,f (sixthFrequencyEquiv p) :=
  (sixthFrequencyEquiv.tsum_eq f).symm

lemma idealGenerator_sixth_eq_primary (I : Id) (hI : CanonicalQuadraticSieve.Supported I) :
    (idealGenerator I)^6=(CompletedGauss.primaryGenerator I)^6 := by
  have he : Ideal.span {idealGenerator I}=Ideal.span {CompletedGauss.primaryGenerator I} :=
    (span_idealGenerator I).trans
      (CompletedGauss.primaryGenerator_spec I
        (supported_primaryGenerator_ne_zero I hI)).1.symm
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp he
  have hh := congrArg (fun a : O=>a^6) hu
  simpa only [mul_pow,CanonicalUnitEuler.unit_pow_six,mul_one] using hh

lemma sixthFrequencyEquiv_primary (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal)
    (hP : CanonicalQuadraticSieve.Supported p.2.val) :
    (sixthFrequencyEquiv p).val=p.1.val*(CompletedGauss.primaryGenerator p.2.val)^6 := by
  rw [sixthFrequencyEquiv_apply,idealGenerator_sixth_eq_primary p.2.val hP]

end SevenEighths.ProbePhysical
end

end OAI
