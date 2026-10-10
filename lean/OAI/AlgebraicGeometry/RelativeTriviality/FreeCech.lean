import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.Cech

namespace OAI

namespace CampanaPeternellSix.ActualCech
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
open RelativeLineCharts
open scoped Polynomial LaurentPolynomial
universe u

lemma laurent_parts (R : Type u) [CommRing R] (f : R[T;T⁻¹]) :
    ∃ p q : R[X], f = p.toLaurent + LaurentPolynomial.invert q.toLaurent := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      obtain ⟨p,q,h⟩ := hf
      obtain ⟨p',q',h'⟩ := hg
      exact ⟨p+p',q+q', by simp only [map_add,h,h']; abel⟩
  | C_mul_T n a =>
      cases n with
      | ofNat n =>
          exact ⟨Polynomial.C a * Polynomial.X^n,0, by simp⟩
      | negSucc n =>
          exact ⟨0,Polynomial.C a * Polynomial.X^(n+1), by
            simp only [map_zero, zero_add, map_mul, Polynomial.toLaurent_C,
              map_mul, map_pow, Polynomial.toLaurent_X, LaurentPolynomial.invert_C,
              LaurentPolynomial.invert_T, LaurentPolynomial.T_pow]
            congr 2
            omega⟩

variable (X : Scheme.{u}) (I : Type u) [Finite I]
def freeProductIso : (SheafOfModules.free I : X.Modules) ≅
    ∏ᶜ (fun _ : I => SheafOfModules.unit X.ringCatSheaf) := by
  classical
  letI := Fintype.ofFinite I
  let f : I → X.Modules := fun _ => SheafOfModules.unit X.ringCatSheaf
  letI : HasBiproduct f := HasBiproduct.of_hasProduct f
  exact (biproduct.isoCoproduct f).symm ≪≫ biproduct.isoProduct f

def freeProjection (i : I) : (SheafOfModules.free I : X.Modules) ⟶
    SheafOfModules.unit X.ringCatSheaf := (freeProductIso X I).hom ≫ Pi.π _ i

local instance freeSectionsModule (U : X.Opens) :
    Module Γ(X,U) Γ((SheafOfModules.free I : X.Modules), U) :=
  ((SheafOfModules.free I : X.Modules).val.obj (op U)).isModule

def freeSectionEquiv (U : X.Opens) :
    Γ((SheafOfModules.free I : X.Modules), U) ≃ₗ[Γ(X,U)] (I → Γ(X,U)) := by
  classical
  letI := Fintype.ofFinite I
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let f : I → X.Modules := fun _ => SheafOfModules.unit X.ringCatSheaf
  exact (F.mapIso (freeProductIso X I) ≪≫ asIso (piComparison F f) ≪≫
    ModuleCat.piIsoPi (F.obj ∘ f)).toLinearEquiv

lemma freeSectionEquiv_apply (U : X.Opens)
    (m : Γ((SheafOfModules.free I : X.Modules), U)) (i : I) :
    freeSectionEquiv X I U m i = (freeProjection X I i).val.app (op U) m := by
  classical
  let := Fintype.ofFinite I
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let f : I → X.Modules := fun _ => SheafOfModules.unit X.ringCatSheaf
  have h : (F.map (freeProductIso X I).hom ≫ piComparison F f ≫
      (ModuleCat.piIsoPi (F.obj ∘ f)).hom) ≫ ModuleCat.ofHom (LinearMap.proj i) =
      F.map ((freeProductIso X I).hom ≫ Pi.π f i) := by
    simp only [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype]
    erw [piComparison_comp_π, ← CategoryTheory.Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom h m

lemma freeSectionEquiv_restrict {U V : X.Opens} (h : U ≤ V)
    (m : Γ((SheafOfModules.free I : X.Modules), V)) (i : I) :
    freeSectionEquiv X I U ((SheafOfModules.free I : X.Modules).val.map
      (homOfLE h).op m) i =
    X.presheaf.map (homOfLE h).op (freeSectionEquiv X I V m i) := by
  erw [freeSectionEquiv_apply, freeSectionEquiv_apply]
  exact ConcreteCategory.congr_hom ((freeProjection X I i).val.naturality (homOfLE h).op) m

variable (R : Type u) [CommRing R]

lemma free_ranges_top :
    leftImage R (SheafOfModules.free I) ⊔ rightImage R (SheafOfModules.free I) = ⊤ := by
  classical
  let E : (scheme R).Modules := SheafOfModules.free I
  apply top_unique
  intro m hm
  change Γ(E,leftOpen R ⊓ rightOpen R) at m
  let c : I → R[T;T⁻¹] := fun i => overlapSectionEquiv R
    (freeSectionEquiv (scheme R) I (leftOpen R ⊓ rightOpen R) m i)
  choose p q hpq using fun i => laurent_parts R (c i)
  let a : Γ(E,leftOpen R) := (freeSectionEquiv (scheme R) I (leftOpen R)).symm
    (fun i => (leftSectionEquiv R).symm (p i))
  let b : Γ(E,rightOpen R) := (freeSectionEquiv (scheme R) I (rightOpen R)).symm
    (fun i => (rightSectionEquiv R).symm (q i))
  let ra : Γ(E,leftOpen R ⊓ rightOpen R) := E.val.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op a
  let rb : Γ(E,leftOpen R ⊓ rightOpen R) := E.val.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op b
  have hsum : ra + rb = m := by
    apply (freeSectionEquiv (scheme R) I (leftOpen R ⊓ rightOpen R)).injective
    ext i
    rw [map_add, Pi.add_apply]
    dsimp only [ra, rb]
    rw [freeSectionEquiv_restrict, freeSectionEquiv_restrict]
    change _ = freeSectionEquiv (scheme R) I (leftOpen R ⊓ rightOpen R) m i
    apply (overlapSectionEquiv R).injective
    rw [map_add, (standard_section_restrictions R).1, (standard_section_restrictions R).2]
    simp only [a,b,LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact (hpq i).symm
  have ha : ra ∈ leftImage R E := ⟨a,rfl⟩
  have hb : rb ∈ rightImage R E := ⟨b,rfl⟩
  exact hsum ▸ Submodule.add_mem_sup ha hb

theorem subsingleton_free_quotient :
    Subsingleton (quotient R (SheafOfModules.free I)) :=
  Submodule.Quotient.subsingleton_iff.mpr (free_ranges_top I R)

end
end CampanaPeternellSix.ActualCech

end OAI
