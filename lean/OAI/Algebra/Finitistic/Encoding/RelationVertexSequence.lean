import OAI.Algebra.Finitistic.Encoding.RelationVertexCoordinates
import OAI.Algebra.Finitistic.Localization.FiniteSumTransport
import OAI.Algebra.Finitistic.Rectification.SourceFiltrationComplex

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.RelationVertexSequence
open QuadraticEncoding RelationBasisCoefficients ExternalTensor.Section4
open ExternalTensor.Section4.SourceFiltration RelationVertexCoordinates
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
local notation "data" => Exactness.data s D₀ D₁ D₂ f g
local instance : HasFiniteBiproducts (RightComplex T) := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts (BiComplex k T) := HasFiniteBiproducts.of_hasFiniteProducts

abbrev arrowFamily : Fin (d+1) → BiComplex k T := fun _ => (columnComplex k T (s).e₁).obj D₀
abbrev relationFamily : RelationIndex P → BiComplex k T := fun _ => (columnComplex k T (s).e₂).obj D₀

def oneSumIso := FiniteSumTransport.iso (vertex P) (tensor P D₀)
  (arrowFamily P D₀) (PathBasisIso.family k d) (fun _ => oneIso P D₀)
def twoSumIso := FiniteSumTransport.iso (vertex P) (tensor P D₀)
  (relationFamily P D₀) (FiniteBasisIso.family (k := k) : RelationIndex P → _) (fun _ => twoIso P D₀)

theorem p_square : (oneSumIso P D₀).hom ≫ (tensor P D₀).map (RelationMatrixSequence.quotient P) =
    (vertex P).map (p0 data) ≫ (zeroIso P D₀).hom := by
  have hg : biproduct.desc (quotientEntry P) = RelationMatrixSequence.quotient P := by
    apply biproduct.hom_ext'
    intro a
    simp [quotientEntry]
  rw [← hg]
  exact FiniteSumTransport.desc_square (vertex P) (tensor P D₀)
    (arrowFamily P D₀) (PathBasisIso.family k d) (fun _ => oneIso P D₀)
    (zeroIso P D₀) (data).pa₀ (quotientEntry P) (RelationVertexCoordinates.p_square P D₀)

theorem q_entry (r : RelationIndex P) (a : Fin (d+1)) :
    biproduct.ι (relationFamily P D₀) r ≫ q0 data ≫ biproduct.π (arrowFamily P D₀) a =
      ∑ b, basisCoefficient P r a b •
        path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D₀ := by
  classical
  change biproduct.ι (data).W r ≫ q0 data ≫ biproduct.π (data).U a = _
  simp only [q0,biproduct.ι_desc_assoc,Preadditive.sum_comp,Category.assoc]
  simp only [biproduct.ι_π]
  rw [Finset.sum_eq_single a]
  · simp [Exactness.data,inducedData,ConcreteQuadraticDiagram.quadratic]
    rfl
  · intro b hb hba
    simp [hba]
  · simp

theorem q_square : (twoSumIso P D₀).hom ≫ (tensor P D₀).map (RelationMatrixSequence.inclusion P) =
    (vertex P).map (q0 data) ≫ (oneSumIso P D₀).hom := by
  apply FiniteSumTransport.matrix_square
  intro r a
  have he := q_entry P D₀ D₁ D₂ f g r a
  change (twoIso P D₀).hom ≫ (tensor P D₀).map (relationEntry P r a) =
    (vertex P).map (biproduct.ι (relationFamily P D₀) r ≫ q0 data ≫
      biproduct.π (arrowFamily P D₀) a) ≫ (oneIso P D₀).hom
  rw [he]
  exact RelationVertexCoordinates.q_square P D₀ r a

def originalSequence : ShortComplex (BiComplex k T) := .mk (q0 data) (p0 data) (q0_p0 data)

def sequenceIso : (originalSequence P D₀ D₁ D₂ f g).map (vertex P) ≅
    (RelationMatrixSequence.sequence P).map (tensor P D₀) :=
  ShortComplex.isoMk (twoSumIso P D₀) (oneSumIso P D₀) (zeroIso P D₀)
    (q_square P D₀ D₁ D₂ f g) (p_square P D₀ D₁ D₂ f g)

/-- The original source-zero p/q maps are a short exact relation sequence at the final vertex. -/
theorem shortExact : ((originalSequence P D₀ D₁ D₂ f g).map (vertex P)).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso (sequenceIso P D₀ D₁ D₂ f g)).2
    (((RelationMatrixSequence.splitting P).map (tensor P D₀)).shortExact)
end LittleFinitistic.RelationVertexSequence

end

end OAI
