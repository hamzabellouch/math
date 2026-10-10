import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalFrequency

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Filter Template TemplateNormAsymptotic HistoryFrequencyBudget InitialCharacterScale

theorem ranges_le_uniform_terminalFrequencyCutoff {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (k j : ℕ) (hj : j ≤ k) (path : List Bool) (f : ℤ) (hf : f ∈ ranges a m j path) :
    f ≠ 0 ∧ f.natAbs ≤ terminalFrequencyCutoff a m k := by
  have hs := (mem_signedRange _ _).mp hf
  refine ⟨hs.1,hs.2.trans ?_⟩
  exact Nat.floor_mono (Real.exp_le_exp.mpr
    (exponent_le_linear ha hm ((Nat.sub_le j path.length).trans hj)))

def actualFrequencyCutoff (k : ℕ) (BD L : ℝ) : ℕ :=
  terminalFrequencyCutoff (BD+20*Real.log (depthScale k)) (wordSize k L : ℝ) k

theorem actualFrequencyCutoff_eventually (k : ℕ) {BD α : ℝ}
    (hBD : 0 ≤ BD) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop,
      (∀j ≤ k,∀path f,
        f ∈ ranges (BD+20*Real.log (depthScale k)) (wordSize k L : ℝ) j path →
          f ≠ 0 ∧ f.natAbs ≤ actualFrequencyCutoff k BD L) ∧
      (∀p : ℕ,Real.exp (α*L) ≤ Real.log p → actualFrequencyCutoff k BD L < p) := by
  let a := BD+20*Real.log (depthScale k)
  have ha : 0 ≤ a := add_nonneg hBD (mul_nonneg (by norm_num)
    (Real.log_nonneg (one_le_depthScale k)))
  filter_upwards [linear_lt_prime_log_eventually (depthScale_pos k) hα
    (linearEnvelope a k) (linearEnvelope_pos ha k).le,
    (wordSize_tendsto k).eventually_ge_atTop 1] with L hL hm
  refine ⟨fun j hj path f hf => ranges_le_uniform_terminalFrequencyCutoff ha hm k j hj path f hf,?_⟩
  intro p hp
  have hp0 : p ≠ 0 := by
    intro he
    subst p
    have hh := Real.exp_pos (α*L)
    simp only [Nat.cast_zero,Real.log_zero] at hp
    linarith
  have hpR : (0:ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp0
  have hexp : Real.exp (linearEnvelope a k*(wordSize k L : ℝ)) < (p:ℝ) := by
    simpa only [wordSize,Real.exp_log hpR] using Real.exp_lt_exp.mpr (hL.trans_le hp)
  have hh : (actualFrequencyCutoff k BD L : ℝ) < p :=
    (Nat.floor_le (Real.exp_pos (linearEnvelope a k*(wordSize k L : ℝ))).le).trans_lt hexp
  exact_mod_cast hh

theorem exists_actual_frequency_cutoff_eventually (k : ℕ) {BD α : ℝ}
    (hBD : 0 ≤ BD) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∃U : ℕ,
      (∀j ≤ k,∀path f,
        f ∈ ranges (BD+20*Real.log (depthScale k)) (wordSize k L : ℝ) j path →
          f ≠ 0 ∧ f.natAbs ≤ U) ∧
      (∀p : ℕ,Real.exp (α*L) ≤ Real.log p → U < p) := by
  filter_upwards [actualFrequencyCutoff_eventually k hBD hα] with L hL
  exact ⟨actualFrequencyCutoff k BD L,hL⟩

end Ostmann.Characters.DiagonalEstimate

end

end OAI
