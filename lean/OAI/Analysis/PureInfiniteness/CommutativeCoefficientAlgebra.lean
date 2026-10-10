import Mathlib

namespace OAI

/-! A finite commuting normal family and its adjoints generate a closed
commutative nonunital C*-algebra in the original ambient algebra. -/

noncomputable section
open scoped IsMulCommutative

namespace WeakPureInfiniteness

variable {D I : Type*} [NonUnitalCStarAlgebra D]

def coefficientAlgebra (c : I → D) : NonUnitalStarSubalgebra ℂ D :=
  (NonUnitalStarAlgebra.adjoin ℂ (Set.range c)).topologicalClosure

instance coefficientAlgebra_closed (c : I → D) : IsClosed (coefficientAlgebra c : Set D) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

def coefficientGenerator (c : I → D) (i : I) : coefficientAlgebra c :=
  ⟨c i, NonUnitalStarSubalgebra.le_topologicalClosure _
    (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)⟩

lemma coefficientAlgebra_commutative (c : I → D) (hn : ∀ i, IsStarNormal (c i))
    (hc : ∀ i j, Commute (c i) (c j)) (hcs : ∀ i j, Commute (c i) (star (c j))) :
    IsMulCommutative (coefficientAlgebra c) := by
  have hbase : IsMulCommutative (NonUnitalStarAlgebra.adjoin ℂ (Set.range c)) := by
    apply NonUnitalStarAlgebra.isMulCommutative_adjoin
    · rintro _ ⟨i, rfl⟩
      exact hn i
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hc i j
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hcs i j
  let := hbase
  exact NonUnitalStarSubalgebra.isMulCommutative_topologicalClosure _

end WeakPureInfiniteness

end

end OAI
