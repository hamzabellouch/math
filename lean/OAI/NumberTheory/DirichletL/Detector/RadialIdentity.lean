import OAI.NumberTheory.DirichletL.Detector.RadialExchange
import OAI.NumberTheory.DirichletL.Detector.CalibrationSupport

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma elementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

lemma actualCongruenceCoefficient_zero_frequency (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA 0=0 := by
  apply actualCongruenceCoefficient_zero_off_calibration S hS A s hA hs hcop
  intro hc
  have hz := (calibrationForSet_coprime_iff S hS 0).mp hc
  obtain ⟨P,hP⟩ := hSne
  exact hz P hP P.zero_mem

theorem actualFrequency_mellin_nonzero (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    (∑'H : NonzeroFrequency,actualCongruenceCoefficient C A s hA H.val*
      paperRadialFourier W (K*elementNorm H.val/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  let : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  have he := radial_sum_exchange W a b ha hW σ (by linarith)
    (fun H : NonzeroFrequency=>actualCongruenceCoefficient C A s hA H.val)
    (fun H=>K*elementNorm H.val/elementNorm ((C.generator*A)*s)) (by
      intro H
      exact div_pos (mul_pos hK (elementNorm_pos H.val H.property))
        (elementNorm_pos _ (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
    (actualFrequency_moment_summable C A s hA hs K hK σ hσ)
  simpa only [Complex.ofReal_mul,Complex.ofReal_div] using he

theorem actualFrequency_mellin (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s))
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    let C := calibrationForSet S hS
    (∑'H : O,actualCongruenceCoefficient C A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  dsimp only
  rw [←actualFrequency_mellin_nonzero (calibrationForSet S hS) A s hA hs W a b ha hW K hK σ hσ]
  symm
  apply (Subtype.val_injective : Function.Injective (fun H : NonzeroFrequency=>H.val)).tsum_eq
    (f:=fun H : O=>actualCongruenceCoefficient (calibrationForSet S hS) A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm (((calibrationForSet S hS).generator*A)*s)))
  intro H hH
  have hn : H≠0 := by
    intro hz
    subst H
    exact hH (by dsimp only; rw [actualCongruenceCoefficient_zero_frequency S hS hSne A s hA hs hcop,zero_mul])
  exact ⟨⟨H,hn⟩,rfl⟩

end SevenEighths.ProbePhysical
end

end OAI
