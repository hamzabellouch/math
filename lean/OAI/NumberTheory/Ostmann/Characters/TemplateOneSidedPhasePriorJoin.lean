import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinEdge
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinExtension
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinNorm
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinSourceMembership

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries HigherBiasSource

theorem sourceBands_coprime {A : ℕ} (E F : Finset (PrimeUpTo A))
    {a b c d : ℝ} (hsep : b≤c ∨ d≤a) :
    ∀q∈boundedInterval E a b,∀r∈boundedInterval F c d,q.val.Coprime r.val := by
  intro q hq r hr
  rcases hsep with hsep | hsep
  · exact boundedInterval_primes_coprime E F hsep hq hr
  · exact (boundedInterval_primes_coprime F E hsep hr hq).symm

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
