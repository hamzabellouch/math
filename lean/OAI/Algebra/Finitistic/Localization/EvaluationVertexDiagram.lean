import OAI.Algebra.Finitistic.Rectification.LeftVertexHomology
import OAI.Algebra.Finitistic.Localization.EvaluationModule

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.EvaluationVertexDiagram
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

abbrev module := ModuleCat.of (B P) X.Evaluation

/-- The vertex of the actual evaluation module is exactly the original vector space. -/
def equiv (i : Fin 3) :
    (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj (module X) ≃ₗ[k] Y where
  toFun z := X.projection i z.val
  invFun y := ⟨X.inclusion i y, by
    erw [VertexFunctor.mem_fixed, X.vertex_smul, X.projection_inclusion]⟩
  left_inv z := by
    apply Subtype.ext
    have hz := (VertexFunctor.mem_fixed _ _ _ _ z.val).1 z.property
    exact (X.vertex_smul i (show X.Evaluation from z.val)).symm.trans hz
  right_inv y := X.projection_inclusion i y
  map_add' x y := (X.projection i).map_add x.val y.val
  map_smul' c z := by
    change X.projection i (algebraMap k (B P) c • z.val) = c • X.projection i z.val
    calc
      X.projection i (algebraMap k (B P) c • (show X.Evaluation from z.val)) =
          X.projection i (c • (show X.Evaluation from z.val)) :=
        congrArg (X.projection i) (IsScalarTower.algebraMap_smul (B P) c (show X.Evaluation from z.val))
      _ = c • X.projection i z.val := (X.projection i).map_smul c (show X.Evaluation from z.val)

def vertexIso (i : Fin 3) := (equiv X i).toModuleIso

def action (a : Fin (d+1)) : ModuleCat.of k Y ⟶ ModuleCat.of k Y :=
  ModuleCat.ofHom (Fin.cases (motive := fun _ => Module.End k Y) (1 : Module.End k Y) X.generator a)

/-- The first arrow family acts by the given representation, including the identity arrow. -/
theorem arrow01_square (a : Fin (d+1))
    (ha : ThreeVertexAlgebra.vertex (composition P) 1 * arrow01 P a = arrow01 P a) :
    (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
      (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a) ha).app (module X) ≫
      (vertexIso X 1).hom = (vertexIso X 0).hom ≫ action X a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change X.projection 1 (arrow01 P a • z.val) =
    (Fin.cases (motive := fun _ => Module.End k Y) (1 : Module.End k Y) X.generator a) (X.projection 0 z.val)
  exact congrArg (X.projection 1) (X.arrow01_smul a (show X.Evaluation from z.val))

/-- The second arrow family has the same specified representation action. -/
theorem arrow12_square (b : Fin (d+1))
    (hb : ThreeVertexAlgebra.vertex (composition P) 2 * arrow12 P b = arrow12 P b) :
    (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
      (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b) hb).app (module X) ≫
      (vertexIso X 2).hom = (vertexIso X 1).hom ≫ action X b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change X.projection 2 (arrow12 P b • z.val) =
    (Fin.cases (motive := fun _ => Module.End k Y) (1 : Module.End k Y) X.generator b) (X.projection 1 z.val)
  exact congrArg (X.projection 2) (X.arrow12_smul b (show X.Evaluation from z.val))
end LittleFinitistic.EvaluationVertexDiagram

end

end OAI
