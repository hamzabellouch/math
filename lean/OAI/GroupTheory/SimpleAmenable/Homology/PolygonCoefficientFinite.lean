import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PlaneCornerCoordinates

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonCoefficientFinite
open Classical

noncomputable def planeCornerLinear {a : ℕ} (ha : 0<a) :
    PlaneStep a →ₗ[ℤ] (PlaneCornerIndex a → PolygonGroupRing) where
  toFun f t := planeCornerCoordinates ha f t
  map_add' f g := by
    funext t
    apply MonoidAlgebra.ext
    ext u
    simp only [planeCornerCoordinates_coeff,Pi.add_apply,MonoidAlgebra.coeff_add,
      Finsupp.add_apply,planeCornerValue_add]
  map_smul' c f := by
    funext t
    apply MonoidAlgebra.ext
    ext u
    simp only [planeCornerCoordinates_coeff,Pi.smul_apply,MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply,planeCornerValue_smul,RingHom.id_apply]

theorem planeCornerCoordinates_translate {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (v : CutRing × CutRing) (t : PlaneCornerIndex a) :
    planeCornerCoordinates ha (PlaneStep.translate v f) t=
      MonoidAlgebra.single (Multiplicative.ofAdd v) 1 * planeCornerCoordinates ha f t := by
  apply MonoidAlgebra.ext
  ext u
  simp only [planeCornerCoordinates_coeff,MonoidAlgebra.coeff_single_mul_apply,
    one_mul,planeCornerValue_translate]
  congr 2
  ext <;> simp [planeVertexPosition,sub_eq_add_neg] <;> ring

noncomputable def planeCornerEmbedding {a : ℕ} (ha : 0<a) :
    (PlaneStep.representation a).asModule →ₗ[PolygonGroupRing]
      (PlaneCornerIndex a → PolygonGroupRing) :=
  MonoidAlgebra.equivariantOfLinearOfComm
    ((planeCornerLinear ha).comp (PlaneStep.representation a).asModuleEquiv.toLinearMap)
    (by
      intro g f
      funext t
      change planeCornerCoordinates ha
        ((PlaneStep.representation a).asModuleEquiv (MonoidAlgebra.single g 1 • f)) t = _
      rw [Representation.asModuleEquiv_map_smul,Representation.asAlgebraHom_single]
      simp only [one_smul]
      exact planeCornerCoordinates_translate ha _ g.toAdd t)

theorem planeCornerEmbedding_injective {a : ℕ} (ha : 0<a) :
    Function.Injective (planeCornerEmbedding ha) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply (PlaneStep.representation a).asModuleEquiv.injective
  apply planeCornerCoordinates_injective_zero ha
  intro t
  exact congrFun hf t

theorem polygon_coefficient_finite {a : ℕ} (ha : 0<a) :
    Module.Finite PolygonGroupRing (PlaneStep.representation a).asModule :=
  Module.Finite.of_injective (planeCornerEmbedding ha) (planeCornerEmbedding_injective ha)

noncomputable instance (a : ℕ) : AddCommGroup (PolygonCoefficientModule a) :=
  inferInstanceAs (AddCommGroup (PlaneStep.representation a).asModule)
noncomputable instance (a : ℕ) : Module ℤ (PolygonCoefficientModule a) :=
  inferInstanceAs (Module ℤ (PlaneStep.representation a).asModule)
noncomputable instance (a : ℕ) : Module PolygonGroupRing (PolygonCoefficientModule a) :=
  inferInstanceAs (Module PolygonGroupRing (PlaneStep.representation a).asModule)

theorem polygon_coefficient_module_finite {a : ℕ} (ha : 0<a) :
    Module.Finite PolygonGroupRing (PolygonCoefficientModule a) := polygon_coefficient_finite ha

end PolygonCoefficientFinite

section NoetherianResolution
open CategoryTheory CategoryTheory.Limits
universe nr

namespace NoetherianResolution
variable {R : Type nr} [CommRing R] [IsNoetherianRing R]

theorem fg_projective_of_free (M : FGModuleCat.{nr} R) [Module.Free R M] :
    Projective M := by
  refine ⟨fun {E X} f e he => ?_⟩
  let F := forget₂ (FGModuleCat.{nr} R) (ModuleCat.{nr} R)
  have hi : Epi (F.map e) := inferInstance
  have hp : Projective (F.obj M) := ModuleCat.projective_of_free (Module.Free.chooseBasis R M)
  obtain ⟨g,hg⟩ := Projective.factors (F.map f) (F.map e)
  refine ⟨FGModuleCat.ofHom g.hom, ?_⟩
  apply F.map_injective
  exact hg

theorem finitePresentation (M : FGModuleCat.{nr} R) : Nonempty (ProjectivePresentation M) := by
  obtain ⟨n,f,hf⟩ := Module.Finite.exists_fin' R M
  have hp : Projective (FGModuleCat.of R (Fin n → R)) := fg_projective_of_free _
  have he : Epi (FGModuleCat.ofHom f) := by
    apply ConcreteCategory.epi_of_surjective
    exact hf
  exact ⟨⟨FGModuleCat.of R (Fin n → R),FGModuleCat.ofHom f⟩⟩

noncomputable local instance : EnoughProjectives (FGModuleCat.{nr} R) where
  presentation := finitePresentation

omit [IsNoetherianRing R] in
theorem forget_projective (M : FGModuleCat.{nr} R) [Projective M] : Projective M.obj := by
  obtain ⟨n,f,hf⟩ := Module.Finite.exists_fin' R M
  let q : FGModuleCat.of R (Fin n → R) ⟶ M := FGModuleCat.ofHom f
  have he : Epi q := ConcreteCategory.epi_of_surjective q hf
  obtain ⟨s,hs⟩ := Projective.factors (𝟙 M) q
  have hlin : f.comp s.hom.hom = LinearMap.id := by
    exact congrArg (fun g => g.hom.hom) hs
  have hp : Module.Projective R M :=
    Module.Projective.of_split s.hom.hom f hlin
  exact ModuleCat.projective_of_categoryTheory_projective M.obj

noncomputable local instance :
    (forget₂ (FGModuleCat.{nr} R) (ModuleCat.{nr} R)).PreservesProjectiveObjects where
  projective_obj {X} h := by
    let := h
    exact forget_projective X

noncomputable def resolution (M : FGModuleCat.{nr} R) : ProjectiveResolution M.obj :=
  (forget₂ (FGModuleCat.{nr} R) (ModuleCat.{nr} R)).mapProjectiveResolution
    (ProjectiveResolution.of M)

instance finite_resolution (M : FGModuleCat.{nr} R) (n : ℕ) :
    Module.Finite R ((resolution M).complex.X n) :=
  inferInstanceAs (Module.Finite R ((ProjectiveResolution.of M).complex.X n))

theorem finite_short_homology (S : ShortComplex (ModuleCat.{nr} R))
    [Module.Finite R S.X₂] : Module.Finite R S.homology := by
  have : Module.Finite R (LinearMap.ker S.g.hom) :=
    Module.Finite.of_injective (LinearMap.ker S.g.hom).subtype Subtype.val_injective
  have : Module.Finite R S.moduleCatLeftHomologyData.H := by
    exact Module.Finite.of_surjective (LinearMap.range S.moduleCatToCycles).mkQ
      (LinearMap.range S.moduleCatToCycles).mkQ_surjective
  exact Module.Finite.of_surjective S.moduleCatHomologyIso.inv.hom
    S.moduleCatHomologyIso.toLinearEquiv.symm.surjective

theorem finite_homology (C : ChainComplex (ModuleCat.{nr} R) ℕ) (n : ℕ)
    [Module.Finite R (C.X n)] : Module.Finite R (C.homology n) := by
  have : Module.Finite R (C.sc n).X₂ := ‹Module.Finite R (C.X n)›
  exact finite_short_homology (C.sc n)

end NoetherianResolution
end NoetherianResolution

end SimpleAmenable
end
end

end OAI
