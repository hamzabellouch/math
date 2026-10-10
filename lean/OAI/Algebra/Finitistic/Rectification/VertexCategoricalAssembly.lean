import OAI.Algebra.Finitistic.Encoding.EncodingModuleAssembly
import OAI.Algebra.Finitistic.Rectification.LeftVertexHomology

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.VertexCategoricalAssembly
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (M N : ModuleCat.{u} (B P))
variable (E : ∀ i : Fin 3,
  (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj M ≅
    (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj N)

abbrev scalar (M : ModuleCat.{u} (B P)) := (ModuleCat.restrictScalars (algebraMap k (B P))).obj M

def vertexEquiv (i : Fin 3) :
    VertexDecomposition.Space (EncodingModuleAssembly.system P) (scalar P M) i ≃ₗ[k]
      VertexDecomposition.Space (EncodingModuleAssembly.system P) (scalar P N) i :=
  (LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) i) M).symm.trans
    ((E i).toLinearEquiv.trans
      (LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) i) N))

/-- Compatible categorical vertex isomorphisms determine a full B-module isomorphism.
The hypotheses are exactly the two finite arrow squares; length-two actions follow. -/
def iso
    (h01 : ∀ a,
      (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
        (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
        (CanonicalArrowCompatibility.arrow01_target P a)).app M ≫ (E 1).hom =
      (E 0).hom ≫ (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
        (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
        (CanonicalArrowCompatibility.arrow01_target P a)).app N)
    (h12 : ∀ b,
      (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
        (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
        (CanonicalArrowCompatibility.arrow12_target P b)).app M ≫ (E 2).hom =
      (E 1).hom ≫ (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
        (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
        (CanonicalArrowCompatibility.arrow12_target P b)).app N) : M ≅ N := by
  let e := EncodingModuleAssembly.equiv P (vertexEquiv P M N E)
    (fun a x => ?_) (fun b x => ?_)
  · exact e.toModuleIso
  · apply Subtype.ext
    have hh := congrArg (fun f => ModuleCat.Hom.hom f
      ((LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) 0) M).symm x)) (h01 a)
    have hh' := congrArg Subtype.val hh
    exact hh'
  · apply Subtype.ext
    have hh := congrArg (fun f => ModuleCat.Hom.hom f
      ((LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) 1) M).symm x)) (h12 b)
    have hh' := congrArg Subtype.val hh
    exact hh'
end LittleFinitistic.VertexCategoricalAssembly

end

end OAI
