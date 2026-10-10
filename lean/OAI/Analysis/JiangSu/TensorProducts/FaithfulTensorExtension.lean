import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.NuclearCommutingExtension

namespace OAI

section

noncomputable section
namespace Pureness
open scoped CStarAlgebra TensorProduct

universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
variable {E T : Type*} [CStarAlgebra E] [CStarAlgebra T]
variable (g : A ⊗[ℂ] B →⋆ₐ[ℂ] T)

def tensorRangeClosure : StarSubalgebra ℂ T := g.range.topologicalClosure
instance tensorRangeClosure_closed : IsClosed (tensorRangeClosure g : Set T) :=
  StarSubalgebra.isClosed_topologicalClosure g.range
instance : CStarAlgebra (tensorRangeClosure g) := inferInstance

def tensorRangeMap : A ⊗[ℂ] B →⋆ₐ[ℂ] tensorRangeClosure g :=
  g.codRestrict _ (fun z => StarSubalgebra.le_topologicalClosure _ ⟨z,rfl⟩)
lemma tensorRangeMap_injective (hg : Function.Injective g) : Function.Injective (tensorRangeMap g) :=
  fun _ _ h => hg (congrArg Subtype.val h)
lemma tensorRangeMap_dense : DenseRange (tensorRangeMap g) := by
  have hd : DenseRange (Set.inclusion (StarSubalgebra.le_topologicalClosure g.range)) := by
    exact (denseRange_inclusion_iff _).2 (by intro x hx; exact hx)
  have hs : Function.Surjective g.rangeRestrict := by
    rintro ⟨x,z,hz⟩
    exact ⟨z,Subtype.ext hz⟩
  exact hd.comp hs.denseRange (continuous_inclusion _)

variable (hA : IsNuclear.{u,v} A) (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E)
variable (hf : Function.Injective f) (hfd : DenseRange f) (hg : Function.Injective g)

def faithfulTensorExtension : E →⋆ₐ[ℂ] T :=
  (tensorRangeClosure g).subtype.comp
    (hA.tensorCompletionEquiv f (tensorRangeMap g) hf (tensorRangeMap_injective g hg)
      hfd (tensorRangeMap_dense g)).toStarAlgHom
lemma faithfulTensorExtension_apply (z : A ⊗[ℂ] B) :
    faithfulTensorExtension g hA f hf hfd hg (f z)=g z := by
  change ((hA.tensorCompletionEquiv f (tensorRangeMap g) hf (tensorRangeMap_injective g hg)
    hfd (tensorRangeMap_dense g) (f z) : tensorRangeClosure g) : T)=g z
  rw [IsNuclear.tensorCompletionEquiv_tensor]
  rfl

end Pureness

end
end

end OAI
