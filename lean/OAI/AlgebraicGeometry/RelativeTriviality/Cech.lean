import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.Charts
import OAI.AlgebraicGeometry.RelativeTriviality.GlobalFunctions
import OAI.AlgebraicGeometry.RelativeTriviality.FiniteSections
import OAI.AlgebraicGeometry.RelativeTriviality.LaurentCech

namespace OAI

namespace CampanaPeternellSix.ActualCech
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Limits
open RelativeLineCharts
universe u
variable (R : Type u) [CommRing R]
 
def coefficientSheaf (E : (scheme R).Modules) :
    TopCat.Sheaf (ModuleCat.{u} R) (scheme R) := by
  let F := ModuleCat.restrictScalars.{u} (RelativeLineGlobalFunctions.scalars R)
  letI : F.IsRightAdjoint := (ModuleCat.extendRestrictScalarsAdj
    (RelativeLineGlobalFunctions.scalars R)).isRightAdjoint
  letI : (Opens.grothendieckTopology (scheme R)).HasSheafCompose F :=
    CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize (F := F) _
  exact (sheafCompose (Opens.grothendieckTopology (scheme R)) F).obj
    ((SheafOfModules.forgetToSheafModuleCat (scheme R).ringCatSheaf (.op ⊤)
      (initialOpOfTerminal isTerminalTop)).obj E)
abbrev overlapModule (E : (scheme R).Modules) : ModuleCat R :=
  (coefficientSheaf R E).obj.obj (op (leftOpen R ⊓ rightOpen R))
def leftImage (E : (scheme R).Modules) : Submodule R (overlapModule R E) :=
  LinearMap.range ((coefficientSheaf R E).obj.map (homOfLE inf_le_left).op).hom
def rightImage (E : (scheme R).Modules) : Submodule R (overlapModule R E) :=
  LinearMap.range ((coefficientSheaf R E).obj.map (homOfLE inf_le_right).op).hom
 

abbrev quotient (E : (scheme R).Modules) :=
  overlapModule R E ⧸ (leftImage R E ⊔ rightImage R E)

open scoped Polynomial LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

def leftInclusion : Spec (.of (ChartRing R)) ⟶ scheme R :=
  Proj.awayι (grading R) (x₀ R) (x₀_mem R) (by decide : 0 < 1)
def rightInclusion : Spec (.of (RightChartRing R)) ⟶ scheme R :=
  Proj.awayι (grading R) (x₁ R) (x₁_mem R) (by decide : 0 < 1)
private lemma isOpenImmersion_iso_inv_comp {X Y Z : Scheme} (e : X ≅ Y)
    (f : X ⟶ Z) [IsOpenImmersion f] : IsOpenImmersion (e.inv ≫ f) :=
  IsOpenImmersion.comp _ _

instance : IsOpenImmersion (leftInclusion R) :=
  isOpenImmersion_iso_inv_comp
    (Proj.basicOpenIsoSpec (grading R) (x₀ R) (x₀_mem R) (by decide : 0 < 1))
    (Proj.basicOpen (grading R) (x₀ R)).ι
instance : IsOpenImmersion (rightInclusion R) :=
  isOpenImmersion_iso_inv_comp
    (Proj.basicOpenIsoSpec (grading R) (x₁ R) (x₁_mem R) (by decide : 0 < 1))
    (Proj.basicOpen (grading R) (x₁ R)).ι
lemma left_range : (leftInclusion R).opensRange = leftOpen R :=
  Proj.opensRange_awayι _ _ _ _
lemma right_range : (rightInclusion R).opensRange = rightOpen R :=
  Proj.opensRange_awayι _ _ _ _
lemma left_image_overlap :
    leftInclusion R ''ᵁ (PrimeSpectrum.basicOpen (coordinate R)) = leftOpen R ⊓ rightOpen R := by
  have hpre : leftInclusion R ⁻¹ᵁ rightOpen R = PrimeSpectrum.basicOpen (coordinate R) := by
    convert! Proj.awayι_preimage_basicOpen (grading R) (x₀_mem R) (by decide : 0 < 1)
      (x₁_mem R) (by decide : 0 < 1) using 1
    simp [leftInclusion, rightOpen, coordinate, HomogeneousLocalization.Away.isLocalizationElem]
    rfl
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, left_range]
lemma right_image_overlap :
    rightInclusion R ''ᵁ (PrimeSpectrum.basicOpen (rightCoordinate R)) = leftOpen R ⊓ rightOpen R := by
  have hpre : rightInclusion R ⁻¹ᵁ leftOpen R = PrimeSpectrum.basicOpen (rightCoordinate R) := by
    convert! Proj.awayι_preimage_basicOpen (grading R) (x₁_mem R) (by decide : 0 < 1)
      (x₀_mem R) (by decide : 0 < 1) using 1
    simp [rightInclusion, leftOpen, rightCoordinate, HomogeneousLocalization.Away.isLocalizationElem]
    rfl
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, right_range, inf_comm]

lemma actual_left_spans (E : (scheme R).Modules) [E.IsQuasicoherent] :
    Submodule.span Γ(scheme R,leftOpen R ⊓ rightOpen R)
      (Set.range (E.presheaf.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op)) = ⊤ := by
  have h := RelativeCech.affine_image_restriction_spans (.of (ChartRing R)) (scheme R) E
    (leftInclusion R) (coordinate R)
  rw [left_image_overlap, Scheme.Hom.image_top_eq_opensRange, left_range] at h
  exact h _
lemma actual_right_spans (E : (scheme R).Modules) [E.IsQuasicoherent] :
    Submodule.span Γ(scheme R,leftOpen R ⊓ rightOpen R)
      (Set.range (E.presheaf.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op)) = ⊤ := by
  have h := RelativeCech.affine_image_restriction_spans (.of (RightChartRing R)) (scheme R) E
    (rightInclusion R) (rightCoordinate R)
  rw [right_image_overlap, Scheme.Hom.image_top_eq_opensRange, right_range] at h
  exact h _

lemma scalar_overlap (a : R) :
    overlapSectionEquiv R ((scheme R).presheaf.map
      (homOfLE (show leftOpen R ⊓ rightOpen R ≤ ⊤ from le_top)).op
      (RelativeLineGlobalFunctions.scalars R a)) = LaurentPolynomial.C a := by
  erw [show (homOfLE (show leftOpen R ⊓ rightOpen R ≤ ⊤ from le_top)) =
    (homOfLE inf_le_left) ≫ (homOfLE (show leftOpen R ≤ ⊤ from le_top)) from rfl,
    op_comp, (scheme R).presheaf.map_comp, CommRingCat.comp_apply,
    (standard_section_restrictions R).1, RelativeLineGlobalFunctions.scalars_left,
    Polynomial.toLaurent_C]

lemma finite_overlap (E : (scheme R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType) :
    Module.Finite Γ(scheme R,leftOpen R ⊓ rightOpen R) Γ(E,leftOpen R ⊓ rightOpen R) := by
  apply RelativeCech.finite_affine_open (scheme R) E hE
  rw [overlap_eq_basic]
  exact Proj.isAffineOpen_basicOpen (grading R) (x₀ R * x₁ R)
    (SetLike.mul_mem_graded (x₀_mem R) (x₁_mem R)) (by decide : 0 < 1+1)

instance overlapAction (E : (scheme R).Modules) :
    Module Γ(scheme R,leftOpen R ⊓ rightOpen R) (overlapModule R E) :=
  (E.val.obj (op (leftOpen R ⊓ rightOpen R))).isModule

instance laurentAction (E : (scheme R).Modules) : Module R[T;T⁻¹] (overlapModule R E) :=
  Module.compHom _ (overlapSectionEquiv R).symm.toRingHom

lemma base_smul (E : (scheme R).Modules) (r : R) (m : overlapModule R E) :
    r • m = (LaurentPolynomial.C r) • m := by
  change ((scheme R).presheaf.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ ⊤ from le_top)).op
    (RelativeLineGlobalFunctions.scalars R r)) • m =
    (overlapSectionEquiv R).symm (LaurentPolynomial.C r) • m
  congr 1
  apply (overlapSectionEquiv R).injective
  rw [RingEquiv.apply_symm_apply, scalar_overlap]

instance laurentTower (E : (scheme R).Modules) :
    IsScalarTower R R[T;T⁻¹] (overlapModule R E) where
  smul_assoc r a m := by
    calc
      (r • a) • m = (LaurentPolynomial.C r * a) • m :=
        congrArg (fun b : R[T;T⁻¹] => b • m) (Algebra.smul_def r a)
      _ = (LaurentPolynomial.C r) • (a • m) := mul_smul _ _ _
      _ = r • (a • m) := (base_smul R E r (a • m)).symm

lemma finite_laurent (E : (scheme R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType) :
    Module.Finite R[T;T⁻¹] (overlapModule R E) := by
  let := finite_overlap R E hE
  let f : Γ(E,leftOpen R ⊓ rightOpen R) →ₛₗ[(overlapSectionEquiv R).toRingHom]
      (overlapModule R E) :=
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => by
        change a • m = (overlapSectionEquiv R).symm (overlapSectionEquiv R a) • m
        rw [RingEquiv.symm_apply_apply] }
  exact Module.Finite.of_surjective f Function.surjective_id

lemma laurent_span_top (E : (scheme R).Modules) (S : Set (overlapModule R E))
    (h : Submodule.span Γ(scheme R,leftOpen R ⊓ rightOpen R) S = ⊤) :
    Submodule.span R[T;T⁻¹] S = ⊤ := by
  apply top_unique
  intro m hm
  clear hm
  have hm' : m ∈ Submodule.span Γ(scheme R,leftOpen R ⊓ rightOpen R) S := by rw [h]; trivial
  induction hm' using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      have he : a • x = (overlapSectionEquiv R a) • x := by
        change a • x = (overlapSectionEquiv R).symm (overlapSectionEquiv R a) • x
        rw [RingEquiv.symm_apply_apply]
      rw [he]
      exact Submodule.smul_mem _ _ ih

lemma left_laurent_spans (E : (scheme R).Modules) [E.IsQuasicoherent] :
    Submodule.span R[T;T⁻¹] (leftImage R E : Set (overlapModule R E)) = ⊤ := by
  apply laurent_span_top
  exact actual_left_spans R E
lemma right_laurent_spans (E : (scheme R).Modules) [E.IsQuasicoherent] :
    Submodule.span R[T;T⁻¹] (rightImage R E : Set (overlapModule R E)) = ⊤ := by
  apply laurent_span_top
  exact actual_right_spans R E

lemma left_stable (E : (scheme R).Modules) (m : overlapModule R E)
    (hm : m ∈ leftImage R E) : LaurentPolynomial.T (R := R) 1 • m ∈ leftImage R E := by
  obtain ⟨y, rfl⟩ := hm
  change Γ(E,leftOpen R) at y
  refine ⟨(leftSectionEquiv R).symm Polynomial.X • y, ?_⟩
  change E.val.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op ((leftSectionEquiv R).symm Polynomial.X • y) =
    @SMul.smul Γ(scheme R,leftOpen R ⊓ rightOpen R) Γ(E,leftOpen R ⊓ rightOpen R)
      inferInstance ((overlapSectionEquiv R).symm (LaurentPolynomial.T 1))
      (E.val.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op y :
        Γ(E,leftOpen R ⊓ rightOpen R))
  erw [E.val.map_smul]
  congr 1
  apply (overlapSectionEquiv R).injective
  change overlapSectionEquiv R ((scheme R).presheaf.map
    (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op
    ((leftSectionEquiv R).symm Polynomial.X)) =
    overlapSectionEquiv R ((overlapSectionEquiv R).symm (LaurentPolynomial.T 1))
  rw [RingEquiv.apply_symm_apply, (standard_section_restrictions R).1,
    RingEquiv.apply_symm_apply, Polynomial.toLaurent_X]

lemma right_stable (E : (scheme R).Modules) (m : overlapModule R E)
    (hm : m ∈ rightImage R E) : LaurentPolynomial.T (R := R) (-1) • m ∈ rightImage R E := by
  obtain ⟨y, rfl⟩ := hm
  change Γ(E,rightOpen R) at y
  refine ⟨(rightSectionEquiv R).symm Polynomial.X • y, ?_⟩
  change E.val.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op ((rightSectionEquiv R).symm Polynomial.X • y) =
    @SMul.smul Γ(scheme R,leftOpen R ⊓ rightOpen R) Γ(E,leftOpen R ⊓ rightOpen R)
      inferInstance ((overlapSectionEquiv R).symm (LaurentPolynomial.T (-1)))
      (E.val.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op y :
        Γ(E,leftOpen R ⊓ rightOpen R))
  erw [E.val.map_smul]
  congr 1
  apply (overlapSectionEquiv R).injective
  change overlapSectionEquiv R ((scheme R).presheaf.map
    (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op
    ((rightSectionEquiv R).symm Polynomial.X)) =
    overlapSectionEquiv R ((overlapSectionEquiv R).symm (LaurentPolynomial.T (-1)))
  rw [RingEquiv.apply_symm_apply, (standard_section_restrictions R).2,
    RingEquiv.apply_symm_apply, Polynomial.toLaurent_X, LaurentPolynomial.invert_T]

theorem finite_actual_cech (E : (scheme R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType) :
    Module.Finite R (quotient R E) := by
  have := finite_laurent R E hE
  obtain ⟨q, hq, ht⟩ := hE
  let := hq
  let := ht
  let := q.isLocallyFree
  have : E.IsQuasicoherent := q.quasiCoherentData.isQuasicoherent
  exact RelativeCech.finite_cech_cokernel R (overlapModule R E) (leftImage R E) (rightImage R E)
    (left_stable R E) (right_stable R E) (left_laurent_spans R E) (right_laurent_spans R E)

end
end CampanaPeternellSix.ActualCech

end OAI
