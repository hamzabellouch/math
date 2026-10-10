import Mathlib

namespace OAI

/-!
# A robust four-row permanent inequality

`Fin 4` labels four sites. A law is represented by real probability masses;
`IsProbability` asserts nonnegativity and total mass one. All row norms use
the uniform counting normalization.
-/

noncomputable section
namespace FourRow
open scoped BigOperators

abbrev Site := Fin 4
abbrev Perm := Equiv.Perm Site
abbrev Law := Perm → ℝ
abbrev Functions := Site → Site → ℝ

def IsProbability (ν : Law) : Prop :=
  (∀ π, 0 ≤ ν π) ∧ ∑ π, ν π = 1

def UniformMarginals (ν : Law) : Prop :=
  ∀ i j : Site, ∑ π, (if π i = j then ν π else 0) = 1 / 4

def totalVariation (ν : Law) : ℝ :=
  (∑ π, |ν π - 1 / 24|) / 2

def lpNorm (p : ℝ) (f : Site → ℝ) : ℝ :=
  ((∑ j, (f j) ^ p) / 4) ^ (1 / p)

def permanentExpectation (ν : Law) (f : Functions) : ℝ :=
  ∑ π, ν π * ∏ i, f i (π i)

theorem robust_permanent :
  ∃ p₀ : ℝ, 4 / 3 < p₀ ∧ p₀ < 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Law,
      IsProbability ν → totalVariation ν < ε → UniformMarginals ν →
      ∀ f : Functions, (∀ i j, 0 ≤ f i j) →
        permanentExpectation ν f ≤ ∏ i, lpNorm p₀ (f i) := by
  sorry

end FourRow
end

end OAI
