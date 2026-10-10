import OAI.NumberTheory.DirichletL.Detector.GramGcdSource
import OAI.NumberTheory.DirichletL.Detector.LowPuncture

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev PrimaryElement := {n : O // Supported (Ideal.span {n}) ∧ λ₀^2∣n-1}

def primaryIdealEquiv : SupportedIdeal≃PrimaryElement where
  toFun I := ⟨primaryGenerator I.val,(supported_span_primaryGenerator_iff _).mpr I.property,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).2⟩
  invFun n := ⟨Ideal.span {n.val},n.property.1⟩
  left_inv I := Subtype.ext (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1
  right_inv n := Subtype.ext (primaryGenerator_span n.val (supported_element_ne_zero _ n.property.1) n.property.2)

lemma primaryCoefficient_nonzero_supported (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (n : O) (hn : primaryCoefficient S hS σ n≠0) :
    Supported (Ideal.span {n}) ∧ λ₀^2∣n-1 := by
  have hp : λ₀^2∣n-1 := by
    by_contra h
    exact hn (by simp [primaryCoefficient,h])
  have hc : IsCoprime (calibrationForSet S hS).generator n := by
    by_contra h
    exact hn (by rw [primaryCoefficient,ite_eq_left hp,gramCoefficientExtension_zero S hS σ n h])
  have hb := calibration_generator_bad S hS hbad
  exact ⟨supported_of_coprime_bad _ n hb.1 hb.2 hc,hp⟩

lemma primary_factor_right (A n : O) (hA : λ₀^2∣A-1) (hAn : λ₀^2∣A*n-1) : λ₀^2∣n-1 := by
  have h := dvd_sub hAn (hA.mul_right n)
  convert h using 1 ; ring

lemma primaryCoefficient_residual (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (A n : O) (hA : λ₀^2∣A-1)
    (hn : primaryCoefficient S hS σ (A*n)≠0) :
    Supported (Ideal.span {n}) ∧ λ₀^2∣n-1 := by
  have hs := primaryCoefficient_nonzero_supported S hS hbad σ (A*n) hn
  have hsp : Supported (Ideal.span {A}*Ideal.span {n}) := by
    rw [Ideal.span_singleton_mul_span_singleton]
    exact hs.1
  exact ⟨((supported_mul_iff _ _).mp hsp).2,primary_factor_right A n hA hs.2⟩

theorem primary_ideal_tsum (f : O→ℂ)
    (hz : ∀n,¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)→f n=0) :
    (∑'I : SupportedIdeal,f (primaryGenerator I.val))=∑'n : O,f n := by
  have he := primaryIdealEquiv.tsum_eq (fun n : PrimaryElement=>f n.val)
  change (∑'I : SupportedIdeal,f (primaryGenerator I.val))=∑'n : PrimaryElement,f n.val at he
  rw [he]
  exact tsum_subtype_eq_of_support_subset (by intro n hn;by_contra h;exact hn (hz n h))

theorem primary_ideal_pair_tsum (f : O→O→ℂ)
    (hl : ∀n m,¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)→f n m=0)
    (hr : ∀n m,¬(Supported (Ideal.span {m}) ∧ λ₀^2∣m-1)→f n m=0) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,f (primaryGenerator I.val) (primaryGenerator J.val))=
      ∑'n : O,∑'m : O,f n m := by
  have hinner (n : O) : (∑'J : SupportedIdeal,f n (primaryGenerator J.val))=∑'m : O,f n m :=
    primary_ideal_tsum (fun m=>f n m) (fun m h=>hr n m h)
  simp_rw [hinner]
  apply primary_ideal_tsum (fun n=>∑'m : O,f n m)
  intro n hn
  simp only [hl n _ hn,tsum_zero]

end SevenEighths.ProbeGramCommon
end

end OAI
