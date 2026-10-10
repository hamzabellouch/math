import Mathlib

namespace OAI

namespace SimpleFInftyOvergroups
universe u

def evalWord {G : Type u} [Group G] {n : ℕ} (g : Fin n → G)
    (w : List (Fin n × Bool)) : G :=
  (w.map fun x => if x.2 then g x.1 else (g x.1)⁻¹).prod

def HasDecidableWordProblem (G : Type u) [Group G] : Prop :=
  ∃ (n : ℕ) (g : Fin n → G), Subgroup.closure (Set.range g) = ⊤ ∧
    ComputablePred (fun w : List (Fin n × Bool) => evalWord g w = 1)

def HasTypeFInfty (H : Type u) [Group H] : Prop :=
  ∃ (X : Type u) (topology : TopologicalSpace X),
    letI : TopologicalSpace X := topology
    ∃ (cw : Topology.CWComplex (Set.univ : Set X)),
      letI : Topology.CWComplex (Set.univ : Set X) := cw
      T2Space X ∧ ConnectedSpace X ∧
      Topology.CWComplex.FiniteType (Set.univ : Set X) ∧
      ∃ (x : X), Nonempty (H ≃* FundamentalGroup X x) ∧
        ∃ (E : Type u) (coverTopology : TopologicalSpace E),
          letI : TopologicalSpace E := coverTopology
          ∃ (p : E → X), IsCoveringMap p ∧ Function.Surjective p ∧ ContractibleSpace E

theorem main (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G →* H, Function.Injective f := by
  sorry

end SimpleFInftyOvergroups

end OAI
