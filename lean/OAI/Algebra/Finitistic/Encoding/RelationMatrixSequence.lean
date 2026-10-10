import OAI.Algebra.Finitistic.Encoding.FiniteBasisIso
import OAI.Algebra.Finitistic.Encoding.RelationPathCoordinates

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.RelationMatrixSequence
open QuadraticEncoding RelationBasisCoefficients
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

abbrev relationIso := FiniteBasisIso.iso (k := k) (V := relationSpace P) (RelationSequence.relationBasis P)
abbrev pathIso := PathBasisIso.iso k d

def inclusion := (relationIso P).hom ≫ (RelationSequence.sequence P).f ≫ (pathIso (k := k) (d := d)).inv

def quotient := (pathIso (k := k) (d := d)).hom ≫ (RelationSequence.sequence P).g

private theorem transported_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {X₁ X₂ X₃ Y₁ Y₂ : C} (e₁ : Y₁ ≅ X₁) (e₂ : Y₂ ≅ X₂)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : f ≫ g = 0) :
    (e₁.hom ≫ f ≫ e₂.inv) ≫ (e₂.hom ≫ g) = 0 := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, h, comp_zero]

private theorem transported_comp_hom {C : Type*} [Category C]
    {X₁ X₂ Y₁ Y₂ : C} (e₁ : Y₁ ≅ X₁) (e₂ : Y₂ ≅ X₂) (f : X₁ ⟶ X₂) :
    e₁.hom ≫ f = (e₁.hom ≫ f ≫ e₂.inv) ≫ e₂.hom := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

def sequence : ShortComplex (ModuleCat.{u} k) :=
  .mk (inclusion P) (quotient P)
    (transported_zero (relationIso P) pathIso _ _ (RelationSequence.sequence P).zero)

/-- The actual independent relation columns and first-arrow path columns are the canonical exact sequence. -/
def sequenceIso : sequence P ≅ RelationSequence.sequence P :=
  ShortComplex.isoMk (relationIso P) (pathIso (k := k) (d := d)) (Iso.refl _)
    (transported_comp_hom (relationIso P) pathIso _) (by simp [sequence,quotient]; rfl)

theorem shortExact : (sequence P).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso (sequenceIso P)).2 (RelationSequence.sequence_shortExact P)

/-- The concrete matrix sequence splits over the base field. -/
def splitting : (sequence P).Splitting := (shortExact P).splittingOfProjective

theorem realized_total_acyclic {C : Type*} [Category C] [Abelian C]
    (F : ModuleCat.{u} k ⥤ CochainComplex C ℤ) [F.Additive] :
    (RectificationTotal.total ((sequence P).map F).g ((sequence P).map F).f
      (Homotopy.ofEq ((sequence P).map F).zero)).Acyclic :=
  RectificationAcyclic.short_exact_total_acyclic _ ((splitting P).map F).shortExact

/-- Each middle column maps by the original length-two path quotient. -/
theorem quotient_injection (a : Fin (d+1)) (w : Arrows k d) :
    (biproduct.ι (PathBasisIso.family k d) a ≫ quotient P).hom w =
      (relationSpace P).mkQ (w ⊗ₜ[k] basis a) := by
  change (relationSpace P).mkQ ((biproduct.ι (PathBasisIso.family k d) a ≫
    (PathBasisIso.iso k d).hom).hom w) = _
  rw [PathBasisIso.injection_apply]

/-- An independent relation column has exactly the source coefficient matrix. -/
theorem inclusion_coordinate (r : RelationIndex P) (a : Fin (d+1)) (c : k) :
    (biproduct.ι (FiniteBasisIso.family (k := k) : RelationIndex P → _) r ≫
      inclusion P ≫ biproduct.π (PathBasisIso.family k d) a).hom c =
        c • ∑ b, basisCoefficient P r a b • basis b := by
  have hp : (pathIso (k := k) (d := d)).inv ≫ biproduct.π (PathBasisIso.family k d) a =
      ModuleCat.ofHom ((LinearMap.proj a).comp RelationPathCoordinates.coordinates.toLinearMap) := by
    simp only [pathIso,PathBasisIso.iso,Iso.trans_inv,Category.assoc,
      ModuleCat.biproductIsoPi_inv_comp_π]
    rfl
  simp only [inclusion, Category.assoc]
  erw [Category.assoc (RelationSequence.sequence P).f, hp]
  change RelationPathCoordinates.coordinates
    (((biproduct.ι (FiniteBasisIso.family (k := k) : RelationIndex P → _) r ≫
      (relationIso P).hom).hom c : relationSpace P) : Paths k d) a = _
  rw [FiniteBasisIso.injection_apply]
  change RelationPathCoordinates.coordinates
    (c • ((RelationSequence.relationBasis P r : relationSpace P) : Paths k d)) a = _
  rw [map_smul]
  exact congrArg (c • ·) (RelationPathCoordinates.basis_coordinate P r a)
end LittleFinitistic.RelationMatrixSequence

end

end OAI
