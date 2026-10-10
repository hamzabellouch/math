import Mathlib

namespace OAI

namespace UniversalFInfinity
universe u

def HasTypeFInfinity (G : Type u) [Group G] : Prop :=
  ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
    (_ : ConnectedSpace X) (cw : Topology.CWComplex (Set.univ : Set X)),
    (∀ n : ℕ, Finite (cw.cell n)) ∧
    (∃ x : X, Nonempty (FundamentalGroup X x ≃* G)) ∧
    ∃ (E : Type u) (_ : TopologicalSpace E) (_ : ContractibleSpace E)
      (p : E → X), Function.Surjective p ∧ IsCoveringMap p

theorem universal_group_of_type_FInfinity :
    ∃ (H : Type u) (groupH : Group H),
      @HasTypeFInfinity H groupH ∧
      ∀ (G : Type u) [Group G] [Group.IsFinitelyPresented G],
        ∃ φ : G →* H, Function.Injective φ := by
  sorry

end UniversalFInfinity

end OAI
