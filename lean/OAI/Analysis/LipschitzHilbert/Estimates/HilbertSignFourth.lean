import OAI.Analysis.LipschitzHilbert.Estimates.HardyPairL4
import OAI.Analysis.LipschitzHilbert.Fourier.HilbertFiniteSymbol

namespace OAI

/-! The fourth-power bound for the sign multiplier on Schwartz functions. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSign_fourth_power (f g : SchwartzMap ℝ ℂ)
    (hzero : (𝓕 f : SchwartzMap ℝ ℂ) 0=0)
    (hfg : ∀ eta, (𝓕 g : SchwartzMap ℝ ℂ) eta=
      hilbertFrequencySign eta*(𝓕 f : SchwartzMap ℝ ℂ) eta) :
    (∫ x, ‖g x‖^4)≤68*(∫ x, ‖f x‖^4) := by
  let a : SchwartzMap ℝ ℂ := (1/2:ℂ) • (f+g)
  let b : SchwartzMap ℝ ℂ := (1/2:ℂ) • (f-g)
  have ha : ∀ eta, eta≤0 → (𝓕 a : SchwartzMap ℝ ℂ) eta=0 := by
    intro eta he
    change (𝓕 ((1/2:ℂ) • (f+g)) : SchwartzMap ℝ ℂ) eta=0
    simp only [FourierTransform.fourier_smul,FourierTransform.fourier_add,smul_apply,
      add_apply,smul_eq_mul,hfg]
    rcases he.eq_or_lt with hz | hn
    · subst eta
      rw [hzero,mul_zero,add_zero,mul_zero]
    · rw [hilbertFrequencySign,ite_eq_right (by linarith)]
      ring
  have hb : ∀ eta, 0≤eta → (𝓕 b : SchwartzMap ℝ ℂ) eta=0 := by
    intro eta he
    change (𝓕 ((1/2:ℂ) • (f-g)) : SchwartzMap ℝ ℂ) eta=0
    simp only [sub_eq_add_neg,FourierTransform.fourier_smul,FourierTransform.fourier_add,
      FourierTransform.fourier_neg,smul_apply,add_apply,neg_apply,smul_eq_mul,hfg]
    rw [hilbertFrequencySign,ite_eq_left he]
    ring
  have hab : a+b=f := by
    ext x
    simp only [a,b,add_apply,sub_apply,smul_apply,smul_eq_mul]
    ring
  have hdiff : a-b=g := by
    ext x
    simp only [a,b,add_apply,sub_apply,smul_apply,smul_eq_mul]
    ring
  have hh := hardyPair_fourth_power a b ha hb
  rwa [hab,hdiff] at hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
