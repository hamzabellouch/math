import Mathlib
import OAI.Analysis.Commutator.CountablyGeneratedCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.DenseRationalStar

variable (A : Type*) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

local instance denseRationalStarNormedAlgebra : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℂ A

local instance denseRationalStarStarModule : StarModule ℚ A where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp

theorem exists_dense_countable : ∃ S : StarSubalgebra ℚ A,
    Countable S ∧ DenseRange (fun a : S => (a:A)) ∧ Complex.I • (1:A)∈S := by
  let s : Set A := Set.range (TopologicalSpace.denseSeq A) ∪ {Complex.I • (1:A)}
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_singleton _)
  let S := StarAlgebra.adjoin ℚ s
  have hms : (Submonoid.closure (s∪star s) : Set A).Countable :=
    countable_submonoidClosure (hs.union (by simpa only [Set.image_star] using hs.image star))
  let M := Submonoid.closure (s∪star s)
  let : Countable M := hms.to_subtype
  have hc : (Submodule.span ℚ (M:Set A) : Set A).Countable := by
    have hr : Set.range (fun a : M => (a:A))=(M:Set A) := by ext a; simp
    have : Countable (Submodule.span ℚ (Set.range (fun a : M => (a:A)))) := inferInstance
    rw [←hr]
    exact Set.countable_coe_iff.mp inferInstance
  have he : (S:Set A)=(Submodule.span ℚ (M:Set A) : Set A) :=
    congrArg (fun N : Submodule ℚ A => (N:Set A)) (StarAlgebra.adjoin_eq_span (R:=ℚ) s)
  have hsc : Countable S := Set.countable_coe_iff.mpr (by rw [he]; exact hc)
  refine ⟨S,hsc,?_,StarAlgebra.subset_adjoin ℚ s (Or.inr (Set.mem_singleton _))⟩
  apply denseRange_subtype_val.mpr
  apply (TopologicalSpace.denseRange_denseSeq A).mono
  intro a ha
  exact StarAlgebra.subset_adjoin ℚ s (Or.inl ha)

end Kadison.DenseRationalStar

end

end
end

end OAI
