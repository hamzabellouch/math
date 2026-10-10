import OAI.Algebra.Finitistic.Ordinary.OrdinaryPairComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.PairComplex
universe u
variable {k : Type u} [Ring k]
variable {O O' T T' : CochainComplex (ModuleCat.{u} k) ℤ}

def map (f : O ⟶ O') (g : T ⟶ T') : complex O T ⟶ complex O' T' where
  f n := ModuleCat.ofHom ((f.f n).hom.prodMap (g.f n).hom)
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (congrArg (fun h => h.hom x.1) (f.comm n (n+1)))
      (congrArg (fun h => h.hom x.2) (g.comm n (n+1)))

theorem biprodIso_natural (f : O ⟶ O') (g : T ⟶ T') :
    map f g ≫ (biprodIso O' T').hom = (biprodIso O T).hom ≫ biprod.map f g := by
  apply biprod.hom_ext
  · simp only [biprodIso,Category.assoc,biprod.lift_fst,biprod.map_fst,biprod.lift_fst_assoc]
    ext n x
    rfl
  · simp only [biprodIso,Category.assoc,biprod.lift_snd,biprod.map_snd,biprod.lift_snd_assoc]
    ext n x
    rfl

/-- Native binary biproducts preserve actual quasi-isomorphisms. -/
theorem biprodMap_quasiIso (f : O ⟶ O') (g : T ⟶ T') [QuasiIso f] [QuasiIso g] :
    QuasiIso (biprod.map f g) := by
  constructor
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap _ i).mpr
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) i
  let : H.Additive := inferInstanceAs ((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) i).Additive)
  let : PreservesFiniteBiproducts H := Functor.preservesFiniteBiproductsOfAdditive H
  let : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  have : IsIso (H.map f) := (quasiIsoAt_iff_isIso_homologyMap f i).mp inferInstance
  have : IsIso (H.map g) := (quasiIsoAt_iff_isIso_homologyMap g i).mp inferInstance
  change IsIso (H.map (biprod.map f g))
  have he : H.map (biprod.map f g) ≫ (H.mapBiprod O' T').hom =
      (H.mapBiprod O T).hom ≫ biprod.map (H.map f) (H.map g) := by
    apply biprod.hom_ext
    · simp only [Functor.mapBiprod_hom,Category.assoc,biprod.lift_fst,biprod.map_fst,biprod.lift_fst_assoc,← H.map_comp]
    · simp only [Functor.mapBiprod_hom,Category.assoc,biprod.lift_snd,biprod.map_snd,biprod.lift_snd_assoc,← H.map_comp]
  have : IsIso (biprod.map (H.map f) (H.map g)) := by
    refine ⟨⟨biprod.map (inv (H.map f)) (inv (H.map g)), ?_, ?_⟩⟩
    · apply biprod.hom_ext <;> simp [Category.assoc]
    · apply biprod.hom_ext <;> simp [Category.assoc]
  have h : IsIso (H.map (biprod.map f g) ≫ (H.mapBiprod O' T').hom) := by
    rw [he]
    infer_instance
  exact (isIso_comp_right_iff _ (H.mapBiprod O' T').hom).mp h

/-- Coordinatewise quasi-isomorphisms give a quasi-isomorphism of the actual direct sum. -/
theorem map_quasiIso (f : O ⟶ O') (g : T ⟶ T') [QuasiIso f] [QuasiIso g] :
    QuasiIso (map f g) := by
  have := biprodMap_quasiIso f g
  have h : QuasiIso (map f g ≫ (biprodIso O' T').hom) := by
    rw [biprodIso_natural]
    infer_instance
  exact (quasiIso_iff_comp_right (map f g) (biprodIso O' T').hom).mp h
end LittleFinitistic.PairComplex

end

end OAI
