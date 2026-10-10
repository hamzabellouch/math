import Mathlib
import OAI.Probability.LogConcave.Complexity.KernelAnalyticNormalizedBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Classical

theorem eventually_forall_of_sequences {X : Type*} [Nonempty X]
    {P Q : ℕ → X → Prop}
    (hne : ∀ᶠ d : ℕ in atTop, ∃x,P d x)
    (hall : ∀f : ℕ → X,(∀ᶠ d : ℕ in atTop,P d (f d)) →
      ∀ᶠ d : ℕ in atTop,Q d (f d)) :
    ∀ᶠ d : ℕ in atTop,∀x,P d x → Q d x := by
  let f : ℕ → X := fun d => if h : ∃x,P d x ∧ ¬Q d x then Classical.choose h
    else if h' : ∃x,P d x then Classical.choose h' else Classical.choice ‹Nonempty X›
  have hp : ∀ᶠ d : ℕ in atTop,P d (f d) := by
    filter_upwards [hne] with d hd
    dsimp only [f]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact Classical.choose_spec hd
  filter_upwards [hall f hp] with d hd x hx
  by_contra hn
  have he : ∃x,P d x ∧ ¬Q d x := ⟨x,hx,hn⟩
  have hf : f d=Classical.choose he := dite_eq_left he
  rw [hf] at hd
  exact (Classical.choose_spec he).2 hd

lemma logPowerEnvelope_rate (C : ℝ) (k : ℕ) (a : ℝ) :
    LogPowerRate (fun d => C*dimensionLog d^k*(d:ℝ)^(-a)) a := by
  have he := ((LogPowerRate.log.pow k).const_mul C).mul (LogPowerRate.power a)
  simpa only [mul_zero,zero_add] using he

lemma logPowerRate_of_envelope {f : ℕ → ℝ} {a C : ℝ} {k : ℕ}
    (hn : ∀ᶠ d in atTop,0≤f d)
    (he : ∀ᶠ d in atTop,f d≤C*dimensionLog d^k*(d:ℝ)^(-a)) :
    LogPowerRate f a := LogPowerRate.of_le (logPowerEnvelope_rate C k a) hn he
end LogConcaveSampling

end

end

end OAI
