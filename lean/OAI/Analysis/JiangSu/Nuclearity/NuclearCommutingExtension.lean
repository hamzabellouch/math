import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.CommutingStarTensor

namespace OAI

section

noncomputable section
namespace Pureness
open scoped TensorProduct

universe u v
variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]

def IsNuclear.tensorCompletionEquiv (hA : IsNuclear.{u, v} A)
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfd : DenseRange f) (hgd : DenseRange g) : E ≃⋆ₐ[ℂ] F :=
  denseStarCompletionEquiv f g hfd hgd (fun z =>
    (hA.faithful_tensor_norm_eq f g hf hg z).symm)

lemma IsNuclear.tensorCompletionEquiv_tensor (hA : IsNuclear.{u, v} A)
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfd : DenseRange f) (hgd : DenseRange g) (z : A ⊗[ℂ] B) :
    hA.tensorCompletionEquiv f g hf hg hfd hgd (f z) = g z :=
  denseStarCompletionEquiv_apply _ _ _ _ _ z

lemma IsNuclear.tensorCompletionEquiv_norm (hA : IsNuclear.{u, v} A)
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfd : DenseRange f) (hgd : DenseRange g) (x : E) :
    ‖hA.tensorCompletionEquiv f g hf hg hfd hgd x‖ = ‖x‖ :=
  denseStarCompletionEquiv_norm _ _ _ _ _ x

end Pureness

end

noncomputable section
namespace CStarAbsorption
open Pureness
open scoped CStarAlgebra TensorProduct

universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]
variable (hD : IsNuclear.{u,u} D) (hs : TopologicallySimple D)
variable {T N : Type*} [CStarAlgebra T] [CStarAlgebra N]
variable (f : D ⊗[ℂ] D →⋆ₐ[ℂ] T) (hf : Function.Injective f) (hd : DenseRange f)
variable (φ ψ : D →⋆ₐ[ℂ] N) (hψ : Function.Injective ψ) (hc : ∀ a b,Commute (φ a) (ψ b))

 def nuclearCommutingHom : T →⋆ₐ[ℂ] N :=
   (commutingTensorClosure φ ψ hc).subtype.comp
     (hD.tensorCompletionEquiv f (commutingTensorClosureMap φ ψ hc) hf
       (commutingTensorClosureMap_injective φ ψ hc hs hψ) hd
       (commutingTensorClosureMap_denseRange φ ψ hc)).toStarAlgHom

 theorem nuclearCommutingHom_tensor (z : D ⊗[ℂ] D) :
    nuclearCommutingHom hD hs f hf hd φ ψ hψ hc (f z)=commutingStarTensorHom φ ψ hc z := by
   change ((hD.tensorCompletionEquiv f (commutingTensorClosureMap φ ψ hc) hf
     (commutingTensorClosureMap_injective φ ψ hc hs hψ) hd
     (commutingTensorClosureMap_denseRange φ ψ hc) (f z)) : N)=_
   rw [IsNuclear.tensorCompletionEquiv_tensor]
   rfl

 theorem nuclearCommutingHom_commute (b : N) (hφb : ∀ a,Commute (φ a) b)
     (hψb : ∀ a,Commute (ψ a) b) (t : T) :
     Commute (nuclearCommutingHom hD hs f hf hd φ ψ hψ hc t) b := by
   refine hd.induction_on t ?_ ?_
   · exact isClosed_eq ((map_continuous _).mul continuous_const)
       (continuous_const.mul (map_continuous _))
   · intro z
     rw [nuclearCommutingHom_tensor]
     induction z using TensorProduct.inductionOn with
     | tmul a d => exact (hφb a).mul_left (hψb d)
     | add z w hz hw => simpa only [map_add] using hz.add_left hw

end CStarAbsorption

end
end

end OAI
