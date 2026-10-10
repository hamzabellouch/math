import OAI.Analysis.Pureness.Tensor.CommutingTensorNorm
import Mathlib.Topology.Algebra.StarSubalgebra

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A B N : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]
variable (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
variable (hc : ∀ a b, Commute (φ a) (ψ b))

def commutingTensorClosure : StarSubalgebra ℂ N :=
  (commutingStarTensorHom φ ψ hc).range.topologicalClosure

instance commutingTensorClosure_closed : IsClosed (commutingTensorClosure φ ψ hc : Set N) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance commutingTensorClosureCStarAlgebra : CStarAlgebra (commutingTensorClosure φ ψ hc) :=
  StarSubalgebra.cstarAlgebra _

def commutingTensorClosureMap : A ⊗[ℂ] B →⋆ₐ[ℂ] commutingTensorClosure φ ψ hc :=
  (commutingStarTensorHom φ ψ hc).codRestrict _
    (fun z => StarSubalgebra.le_topologicalClosure _ ⟨z,rfl⟩)

lemma commutingTensorClosureMap_coe (z : A ⊗[ℂ] B) :
    (commutingTensorClosureMap φ ψ hc z : N) = commutingStarTensorHom φ ψ hc z := rfl

lemma commutingTensorClosureMap_injective [Nontrivial A]
    (hsimple : TopologicallySimple A) (hψ : Function.Injective ψ) :
    Function.Injective (commutingTensorClosureMap φ ψ hc) := by
  intro x y h
  exact commutingStarTensorHom_injective hsimple φ ψ hψ hc (congrArg Subtype.val h)

lemma commutingTensorClosureMap_denseRange :
    DenseRange (commutingTensorClosureMap φ ψ hc) := by
  have hd : DenseRange (Set.inclusion
      (StarSubalgebra.le_topologicalClosure (commutingStarTensorHom φ ψ hc).range)) := by
    exact (denseRange_inclusion_iff _).mpr Set.Subset.rfl
  have hs : Function.Surjective (commutingStarTensorHom φ ψ hc).rangeRestrict := by
    rintro ⟨x,z,hz⟩
    exact ⟨z,Subtype.ext hz⟩
  exact hd.comp hs.denseRange (continuous_inclusion _)

lemma commutingTensorClosureMap_isometry [Nontrivial A]
    (hsimple : TopologicallySimple A) (hψ : Function.Injective ψ) :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    Isometry (commutingTensorClosureMap φ ψ hc) := by
  let := commutingTensorNormedRing hsimple φ ψ hψ hc
  apply AddMonoidHomClass.isometry_of_norm
  intro z
  rfl

lemma commutingTensorClosure_eq_generated :
    commutingTensorClosure φ ψ hc =
      (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range ψ)).topologicalClosure := by
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_minimal
      _ (StarSubalgebra.isClosed_topologicalClosure _)
    rintro _ ⟨z,rfl⟩
    apply StarSubalgebra.le_topologicalClosure
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change φ a*ψ b ∈ StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range ψ)
      apply mul_mem
      · exact StarAlgebra.subset_adjoin (R := ℂ) _ (Set.mem_union_left _ ⟨a,rfl⟩)
      · exact StarAlgebra.subset_adjoin (R := ℂ) _ (Set.mem_union_right _ ⟨b,rfl⟩)
    | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy
  · apply StarSubalgebra.topologicalClosure_minimal _ (commutingTensorClosure_closed φ ψ hc)
    apply StarAlgebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨b,rfl⟩)
    · exact StarSubalgebra.le_topologicalClosure _ ⟨a ⊗ₜ[ℂ] (1 : B),by
        simp [commutingStarTensorHom_tmul]⟩
    · exact StarSubalgebra.le_topologicalClosure _ ⟨(1 : A) ⊗ₜ[ℂ] b,by
        simp [commutingStarTensorHom_tmul]⟩
end CuntzPureness

end

end OAI
