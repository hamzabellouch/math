import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSizeFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateNormAsymptoticPrecision

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Filter HistoryFrequencyLabels HistoryFrequencyBudget TemplateNormAsymptotic

def terminalFrequencyCutoff (a m : ℝ) (j : ℕ) : ℕ :=
  ⌊Real.exp (linearEnvelope a j*m)⌋₊

theorem ranges_le_terminalFrequencyCutoff {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (j : ℕ) (path : List Bool) (f : ℤ) (hf : f ∈ ranges a m j path) :
    f≠0 ∧ f.natAbs ≤ terminalFrequencyCutoff a m j := by
  have hs := (mem_signedRange _ _).mp hf
  refine ⟨hs.1,hs.2.trans ?_⟩
  exact Nat.floor_mono (Real.exp_le_exp.mpr (exponent_le_linear ha hm (Nat.sub_le j path.length)))

theorem terminalFrequencyCutoff_lt_prime_eventually {z α a : ℝ}
    (hz : 0<z) (hα : 0<α) (ha : 0 ≤ a) (j : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (∀path f,f ∈ ranges a (⌊z*L⌋₊ : ℝ) j path →
        f≠0 ∧ f.natAbs ≤ terminalFrequencyCutoff a (⌊z*L⌋₊ : ℝ) j) ∧
      ∀p : ℕ,p.Prime → Real.exp (α*L) ≤ Real.log p →
        terminalFrequencyCutoff a (⌊z*L⌋₊ : ℝ) j<p := by
  filter_upwards [linear_lt_prime_log_eventually hz hα (linearEnvelope a j)
    (linearEnvelope_pos ha j).le,(word_tendsto hz).eventually_ge_atTop 1] with L hL hm
  refine ⟨fun path f hf => ranges_le_terminalFrequencyCutoff ha hm j path f hf,?_⟩
  intro p hp hlog
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have he : Real.exp (linearEnvelope a j*(⌊z*L⌋₊ : ℝ))<(p:ℝ) := by
    simpa only [Real.exp_log hpR] using Real.exp_lt_exp.mpr (hL.trans_le hlog)
  have hf := Nat.floor_le (Real.exp_pos (linearEnvelope a j*(⌊z*L⌋₊ : ℝ))).le
  have ht : (terminalFrequencyCutoff a (⌊z*L⌋₊ : ℝ) j:ℝ)<p := hf.trans_lt he
  exact_mod_cast ht

end Ostmann.Characters.Template

end

end OAI
