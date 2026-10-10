import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
variable {I : Type*} [Fintype I] [DecidableEq I]

def indexedFixedPhase (D : I → I → ℤ) (p : I → ℕ) (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ)
    (ν : I → ℕ → ℂ) (L S : I) : ℂ :=
  ∏ i ∈ frozenVertices L S, ν i (p i) *
    ∏ h ∈ frozenVertices L S, χ i (p i) (p h) ^ D i h

def indexedLongUnary (D : I → I → ℤ) (p : I → ℕ) (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ)
    (ν : I → ℕ → ℂ) (L S : I) (q : ℕ) : ℂ :=
  ν L q * (∏ h ∈ frozenVertices L S, χ L q (p h) ^ D L h) *
    (∏ i ∈ frozenVertices L S, χ i (p i) q ^ D i L) * indexedFixedPhase D p χ ν L S

def indexedShortUnary (D : I → I → ℤ) (p : I → ℕ) (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ)
    (ν : I → ℕ → ℂ) (L S : I) (r : ℕ) : ℂ :=
  ν S r * (∏ h ∈ frozenVertices L S, χ S r (p h) ^ D S h) *
    (∏ i ∈ frozenVertices L S, χ i (p i) r ^ D i S)

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
