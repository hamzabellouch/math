import OAI.Algebra.Finitistic.Rectification.SourceFiltrationReal

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- An isomorphism of the two input columns gives an isomorphism of actual cones. -/
def coneIso {X Y X' Y' : BiComplex k B} (p : X ⟶ Y) (p' : X' ⟶ Y')
    (a : X ≅ X') (b : Y ≅ Y') (w : a.hom ≫ p' = p ≫ b.hom) :
    mappingCone p ≅ mappingCone p' where
  hom := coneMap p p' a.hom b.hom w
  inv := coneMap p' p a.inv b.inv (by
    apply (cancel_epi a.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [w, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := by rw [← coneMap_comp]; simp
  inv_hom_id := by rw [← coneMap_comp]; simp

variable (X : BiComplex k B)

theorem zeroCone_inclusion_product (n : ℤ) :
    (mappingCone.inr (0 : Z ⟶ X)).f n ≫
      ((homotopyCofiber.XIsoBiprod (0 : Z ⟶ X) n (n+1) rfl) ≪≫
        ModuleCat.biprodIsoProd _ _).hom =
      ModuleCat.ofHom (LinearMap.inr (Enveloping k B) (Z.X (n+1)) (X.X n)) := by
  erw [Iso.trans_hom, ← Category.assoc, cone_inr_termIso]
  exact inr_prod _ _

theorem zeroCone_inclusion_bijective (n : ℤ) :
    Function.Bijective ((mappingCone.inr (0 : Z ⟶ X)).f n) := by
  let e := ((homotopyCofiber.XIsoBiprod (0 : Z ⟶ X) n (n+1) rfl) ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv
  have he (x : X.X n) : e ((mappingCone.inr (0 : Z ⟶ X)).f n x) = (0,x) :=
    congrArg (fun a => a x) (zeroCone_inclusion_product X n)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have := congrArg e hxy
    simpa only [he] using congrArg Prod.snd this
  · intro y
    refine ⟨(e y).2, e.injective ?_⟩
    rw [he]
    exact Prod.ext (Subsingleton.elim _ _) rfl

instance zeroCone_inclusion_isIso : IsIso (mappingCone.inr (0 : Z ⟶ X)) := by
  have (n : ℤ) : IsIso ((mappingCone.inr (0 : Z ⟶ X)).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (zeroCone_inclusion_bijective X n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The ordinary two-column total identifies with the three-column API having
zero relation column; its zero-column inclusion is unchanged. -/
def twoColumnIso {Y : BiComplex k B} (p : X ⟶ Y)
    (h : Homotopy ((0 : Z ⟶ X) ≫ p) 0) : mappingCone p ≅ total p 0 h :=
  coneIso p (rectifyingMap p 0 h) (asIso (mappingCone.inr (0 : Z ⟶ X)))
    (Iso.refl _) (by simp [rectifyingMap])

theorem twoColumnIso_inclusion {Y : BiComplex k B} (p : X ⟶ Y)
    (h : Homotopy ((0 : Z ⟶ X) ≫ p) 0) :
    mappingCone.inr p ≫ (twoColumnIso X p h).hom = inclusion p 0 h := by
  apply HomologicalComplex.hom_ext
  intro n
  change (mappingCone.inr p).f n ≫
    (coneMap p (rectifyingMap p 0 h) (mappingCone.inr (0 : Z ⟶ X)) (𝟙 Y) _).f n =
      (mappingCone.inr (rectifyingMap p 0 h)).f n
  erw [coneMap_inr, id_f, Category.id_comp]

variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

def f1ConeIso : mappingCone (p1 t) ≅ total (p1 t) 0 (h1 t) :=
  twoColumnIso _ _ _
def grade1ConeIso : mappingCone (pGrade1 t) ≅ total (pGrade1 t) 0 (hGrade1 t) :=
  twoColumnIso _ _ _
end ExternalTensor.Section4.SourceFiltration

end

end OAI
