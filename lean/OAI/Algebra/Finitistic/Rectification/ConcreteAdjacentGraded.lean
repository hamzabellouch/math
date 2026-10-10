import OAI.Algebra.Finitistic.Rectification.AdjacentArrowSum
import OAI.Algebra.Finitistic.Rectification.RectificationAcyclic

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.ConcreteAdjacentGraded
open ExternalTensor.Section4 QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D : RightComplex (QuadraticEncoding.B P))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P

def arrow01Sum : (⨁ fun _ : Fin (d+1) => (columnComplex k T (s).e₁).obj D) ⟶
    (columnComplex k T (s).e₀).obj D :=
  biproduct.desc (fun a => path k T (s).e₀ (s).e₁ (arrow01 P a) ((s).ha a) D)

def arrow12Sum : (⨁ fun _ : Fin (d+1) => (columnComplex k T (s).e₂).obj D) ⟶
    (columnComplex k T (s).e₁).obj D :=
  biproduct.desc (fun b => path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D)

theorem vertex1_arrow01_isIso :
    IsIso ((AdjacentArrowSum.vertexComplex (composition P) 1).map (arrow01Sum P D)) := by
  let F := AdjacentArrowSum.vertexComplex (composition P) 1
  have hdesc := AdjacentArrowSum.desc_isIso (composition P) D 1 0 d
    (CornerSpaces.corner10Equiv (composition P)) (arrow01 P) ((s).ha)
    (CornerArrowCoordinates.arrow01_coordinate P)
  let : IsIso (biproduct.desc (fun a => F.map
    (path k T (s).e₀ (s).e₁ (arrow01 P a) ((s).ha a) D))) := hdesc
  change IsIso (F.map (biproduct.desc _))
  rw [← biproduct.mapBiproduct_hom_desc,isIso_comp_left_iff]
  exact hdesc

theorem vertex2_arrow12_isIso :
    IsIso ((AdjacentArrowSum.vertexComplex (composition P) 2).map (arrow12Sum P D)) := by
  let F := AdjacentArrowSum.vertexComplex (composition P) 2
  have hdesc := AdjacentArrowSum.desc_isIso (composition P) D 2 1 d
    (CornerSpaces.corner21Equiv (composition P)) (arrow12 P) ((s).hb)
    (CornerArrowCoordinates.arrow12_coordinate P)
  let : IsIso (biproduct.desc (fun b => F.map
    (path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D))) := hdesc
  change IsIso (F.map (biproduct.desc _))
  rw [← biproduct.mapBiproduct_hom_desc,isIso_comp_left_iff]
  exact hdesc

/-- The first adjacent graded cone is acyclic for the actual arrow map. -/
theorem vertex1_cone_acyclic :
    (CochainComplex.mappingCone
      ((AdjacentArrowSum.vertexComplex (composition P) 1).map (arrow01Sum P D))).Acyclic := by
  let := vertex1_arrow01_isIso P D
  exact RectificationAcyclic.cone_acyclic _

/-- The second adjacent graded cone is acyclic for the actual arrow map. -/
theorem vertex2_cone_acyclic :
    (CochainComplex.mappingCone
      ((AdjacentArrowSum.vertexComplex (composition P) 2).map (arrow12Sum P D))).Acyclic := by
  let := vertex2_arrow12_isIso P D
  exact RectificationAcyclic.cone_acyclic _
end LittleFinitistic.ConcreteAdjacentGraded

end

end OAI
