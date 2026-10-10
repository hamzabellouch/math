import Mathlib.CategoryTheory.Abelian.Projective.Resolution

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y Z : C}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)

omit [Abelian C] in
private theorem compose_square {A B D X Y Z : C}
    (p : A ⟶ X) (q : B ⟶ Y) (r : D ⟶ Z)
    (f : A ⟶ B) (g : B ⟶ D) (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (hp : p ≫ a = f ≫ q) (hq : q ≫ b = g ≫ r) (hc : p ≫ c = (f ≫ g) ≫ r) :
    p ≫ c = p ≫ a ≫ b := by
  calc
    p ≫ c = (f ≫ g) ≫ r := hc
    _ = f ≫ g ≫ r := Category.assoc _ _ _
    _ = f ≫ q ≫ b := congrArg (fun z => f ≫ z) hq.symm
    _ = (f ≫ q) ≫ b := (Category.assoc _ _ _).symm
    _ = (p ≫ a) ≫ b := congrArg (fun z => z ≫ b) hp.symm
    _ = p ≫ a ≫ b := Category.assoc _ _ _

def resolutionEndpointMap (f : P.complex ⟶ Q.complex) : X ⟶ Y :=
  P.isColimitCokernelCofork.desc (CokernelCofork.ofπ (f.f 0 ≫ Q.π.f 0) (by
    rw [← Category.assoc, ← f.comm 1 0, Category.assoc,
      Q.complex_d_comp_π_f_zero, comp_zero]))

@[reassoc] theorem resolutionEndpointMap_augmentation (f : P.complex ⟶ Q.complex) :
    P.π.f 0 ≫ resolutionEndpointMap P Q f = f.f 0 ≫ Q.π.f 0 :=
  Cofork.IsColimit.π_desc P.isColimitCokernelCofork

theorem resolutionEndpointMap_id : resolutionEndpointMap P P (𝟙 _) = 𝟙 X := by
  apply (cancel_epi (P.π.f 0)).1
  erw [resolutionEndpointMap_augmentation]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem resolutionEndpointMap_comp (T : ProjectiveResolution Z)
    (f : P.complex ⟶ Q.complex) (g : Q.complex ⟶ T.complex) :
    resolutionEndpointMap P T (f ≫ g) = resolutionEndpointMap P Q f ≫ resolutionEndpointMap Q T g := by
  apply (cancel_epi (P.π.f 0)).1
  exact compose_square (show P.complex.X 0 ⟶ X from P.π.f 0)
    (show Q.complex.X 0 ⟶ Y from Q.π.f 0) (show T.complex.X 0 ⟶ Z from T.π.f 0)
    (f.f 0) (g.f 0) _ _ _ (resolutionEndpointMap_augmentation P Q f)
    (resolutionEndpointMap_augmentation Q T g) (resolutionEndpointMap_augmentation P T (f ≫ g))

def resolutionEndpointIso (e : P.complex ≅ Q.complex) : X ≅ Y where
  hom := resolutionEndpointMap P Q e.hom
  inv := resolutionEndpointMap Q P e.inv
  hom_inv_id := by erw [← resolutionEndpointMap_comp, e.hom_inv_id, resolutionEndpointMap_id]
  inv_hom_id := by erw [← resolutionEndpointMap_comp, e.inv_hom_id, resolutionEndpointMap_id]

@[reassoc] theorem resolutionEndpointIso_augmentation (e : P.complex ≅ Q.complex) :
    P.π.f 0 ≫ (resolutionEndpointIso P Q e).hom = e.hom.f 0 ≫ Q.π.f 0 :=
  resolutionEndpointMap_augmentation P Q e.hom

theorem resolutionEndpointIso_hom_unique (e : P.complex ≅ Q.complex) (a : X ⟶ Y)
    (ha : P.π.f 0 ≫ a = e.hom.f 0 ≫ Q.π.f 0) :
    (resolutionEndpointIso P Q e).hom = a := by
  apply (cancel_epi (P.π.f 0)).1
  erw [resolutionEndpointIso_augmentation, ha]

end ArExplicit.ResolutionProducts

end

end OAI
