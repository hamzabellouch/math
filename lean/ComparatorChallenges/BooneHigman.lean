import Mathlib

namespace OAI

namespace FiniteAlgebraicEnvelopes

universe u

abbrev Word (generatorCount : ℕ) := List (Fin generatorCount × Bool)

def evalWord {GroupType : Type u} [Group GroupType] {generatorCount : ℕ}
    (generators : Fin generatorCount → GroupType) (word : Word generatorCount) : GroupType :=
  (word.map fun letter =>
    if letter.2 then generators letter.1 else (generators letter.1)⁻¹).prod

def HasDecidableWordProblem (GroupType : Type u) [Group GroupType] : Prop :=
  ∃ (generatorCount : ℕ) (generators : Fin generatorCount → GroupType),
    Subgroup.closure (Set.range generators) = ⊤ ∧
    ComputablePred (fun word : Word generatorCount => evalWord generators word = 1)

def EmbedsInFinitelyPresentedSimpleGroup (GroupType : Type u) [Group GroupType] : Prop :=
  ∃ (TargetGroup : Type u) (_ : Group TargetGroup),
    Group.IsFinitelyPresented TargetGroup ∧ IsSimpleGroup TargetGroup ∧
    ∃ embedding : GroupType →* TargetGroup, Function.Injective embedding

theorem main (GroupType : Type u) [Group GroupType] [Group.FG GroupType] :
    HasDecidableWordProblem GroupType ↔ EmbedsInFinitelyPresentedSimpleGroup GroupType := by
  sorry

end FiniteAlgebraicEnvelopes

end OAI
