import OAI.Algebra.Finitistic.Rectification.VertexTensorLinear

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.RelationVertexCoordinates
open QuadraticEncoding RelationBasisCoefficients ExternalTensor.Section4
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D : RightComplex (QuadraticEncoding.B P))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
abbrev vertex := AdjacentArrowSum.vertexComplex (composition P) 2
abbrev tensor := TensorComplex.tensorFunctor (k := k) D

def zeroIso := CornerPathTransport.coordinateIso (composition P) D 2 0
  (CornerSpaces.corner20Equiv (composition P))
def oneIso := CornerPathTransport.coordinateIso (composition P) D 2 1
  (CornerSpaces.corner21Equiv (composition P))
def twoIso := CornerPathTransport.coordinateIso (composition P) D 2 2
  (CornerSpaces.diagonalEquiv (composition P) 2)

def quotientEntry (a : Fin (d+1)) :=
  biproduct.ι (PathBasisIso.family k d) a ≫ RelationMatrixSequence.quotient P

def relationEntry (r : RelationIndex P) (a : Fin (d+1)) :=
  biproduct.ι (FiniteBasisIso.family (k := k) : RelationIndex P → _) r ≫
    RelationMatrixSequence.inclusion P ≫ biproduct.π (PathBasisIso.family k d) a

theorem relationEntry_eq (r : RelationIndex P) (a : Fin (d+1)) :
    relationEntry P r a = ∑ b, basisCoefficient P r a b • TensorArrowSum.insertion k d b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (biproduct.ι _ r ≫ RelationMatrixSequence.inclusion P ≫ biproduct.π _ a).hom c = _
  rw [RelationMatrixSequence.inclusion_coordinate]
  simp only [Finset.smul_sum,ModuleCat.hom_sum,ModuleCat.hom_smul,
    LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro b hb
  rw [TensorArrowSum.insertion_apply]
  simp only [smul_smul,mul_comm]

/-- The source-zero p entry becomes the actual length-two path quotient. -/
theorem p_square (a : Fin (d+1)) :
    (oneIso P D).hom ≫ (tensor P D).map (quotientEntry P a) =
      (vertex P).map (path k T (s).e₀ (s).e₁ (arrow01 P a) ((s).ha a) D) ≫
        (zeroIso P D).hom := by
  apply CornerPathTransport.path_square
  intro x
  change (CornerSpaces.corner20Equiv (composition P))
    (CornerColumnPaths.cornerMap (composition P) 2 0 1 (arrow01 P a) ((s).ha a) x) =
    (quotientEntry P a).hom ((CornerSpaces.corner21Equiv (composition P)) x)
  rw [show (quotientEntry P a).hom ((CornerSpaces.corner21Equiv (composition P)) x) =
    (relationSpace P).mkQ (((CornerSpaces.corner21Equiv (composition P)) x) ⊗ₜ[k] basis a)
      from RelationMatrixSequence.quotient_injection P a _]
  simpa only [LinearEquiv.symm_apply_apply] using
    CornerArrowCoordinates.lengthTwo_coordinate P a ((CornerSpaces.corner21Equiv (composition P)) x)

/-- The source-zero q entry uses the original coefficients and actual b-arrow maps. -/
theorem q_square (r : RelationIndex P) (a : Fin (d+1)) :
    (twoIso P D).hom ≫ (tensor P D).map (relationEntry P r a) =
      (vertex P).map (∑ b, basisCoefficient P r a b •
        path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D) ≫ (oneIso P D).hom := by
  have hb (b : Fin (d+1)) :
      (twoIso P D).hom ≫ (tensor P D).map (TensorArrowSum.insertion k d b) =
      (vertex P).map (path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D) ≫
        (oneIso P D).hom := by
    refine CornerPathTransport.path_square (composition P) D 2 1 2
      (CornerSpaces.diagonalEquiv (composition P) 2) (CornerSpaces.corner21Equiv (composition P))
      (arrow12 P b) ((s).hb b) (TensorArrowSum.insertion k d b).hom ?_
    intro x
    change (CornerSpaces.corner21Equiv (composition P))
      (CornerColumnPaths.cornerMap (composition P) 2 1 2 (arrow12 P b) ((s).hb b) x) =
        (TensorArrowSum.insertion k d b).hom ((CornerSpaces.diagonalEquiv (composition P) 2) x)
    rw [TensorArrowSum.insertion_apply]
    simpa only [LinearEquiv.symm_apply_apply] using
      CornerArrowCoordinates.arrow12_coordinate P b ((CornerSpaces.diagonalEquiv (composition P) 2) x)
  rw [relationEntry_eq]
  simp only [Functor.map_sum,Functor.map_smul,Preadditive.comp_sum,Linear.comp_smul]
  refine (Finset.sum_congr rfl
    (fun b _ => congrArg (basisCoefficient P r a b • ·) (hb b))).trans ?_
  refine (Finset.sum_congr rfl (fun b _ =>
    (Linear.smul_comp _ _ _ (basisCoefficient P r a b)
      ((vertex P).map (path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D))
      (oneIso P D).hom).symm)).trans ?_
  exact (Preadditive.sum_comp Finset.univ
      (fun b => basisCoefficient P r a b •
        (vertex P).map (path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D))
      (oneIso P D).hom).symm
end LittleFinitistic.RelationVertexCoordinates

end

end OAI
