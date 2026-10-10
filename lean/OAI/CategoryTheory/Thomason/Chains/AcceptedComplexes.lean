import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Representation

namespace OAI

/-! The bundled-group and carrier-and-instance presentations of augmented
 directed complexes have the same positive tables and strict realization. -/

namespace Thomason.Construction.DirectedComplex

open CategoryTheory

universe u

/-- Express a directed complex using its chain carriers and group instances. -/
def toAccepted (K : DirectedComplex.{u}) : Thomason.DirectedComplex.{u} where
  Chain n := K.group n
  group _ := inferInstance
  d := K.differential
  d_d := K.differential_squared
  augmentation := K.augmentation
  augmentation_d := K.augmentation_differential
  positive := K.positive

/-- Bundle the chain groups of a carrier-and-instance directed complex. -/
def ofAccepted (K : Thomason.DirectedComplex.{u}) : DirectedComplex.{u} where
  group n := AddCommGrpCat.of (K.Chain n)
  differential := K.d
  differential_squared := K.d_d
  augmentation := K.augmentation
  augmentation_differential := K.augmentation_d
  positive := K.positive

/-- A positive chain map is unchanged on each chain group by the conversion. -/
def Hom.toAccepted {K L : DirectedComplex.{u}} (f : Hom K L) :
    Thomason.DirectedComplex.Hom K.toAccepted L.toAccepted where
  map := f.app
  map_d := f.differential
  map_augmentation := f.augmentation
  map_positive n _ hx := f.positive n hx

/-- Positive chain maps also admit the bundled-group presentation. -/
def Hom.ofAccepted {K L : Thomason.DirectedComplex.{u}} (f : Thomason.DirectedComplex.Hom K L) :
    Hom (ofAccepted K) (ofAccepted L) where
  app := f.map
  differential := f.map_d
  augmentation := f.map_augmentation
  positive n _ hx := f.map_positive n _ hx

namespace Cell

variable {K L : DirectedComplex.{u}}

/-- Transpose the degree and boundary indices of a positive globular table. -/
def toAccepted (x : Cell K) : Thomason.DirectedComplex.Table K.toAccepted where
  row n a := x.table a n
  positive n a := x.positive a n
  boundary n a := x.boundary a n
  augmentation := x.augmentation
  bounded := x.finite_support

/-- Express a positive table in the Boolean-face presentation. -/
def ofAccepted (x : Thomason.DirectedComplex.Table K.toAccepted) : Cell K where
  table a n := x.row n a
  positive a n := x.positive n a
  boundary a n := x.boundary n a
  augmentation := x.augmentation
  finite_support := x.bounded

/-- The table conversion preserves all chains, including zero upper chains. -/
def acceptedEquiv (K : DirectedComplex.{u}) : Cell K ≃ Thomason.DirectedComplex.Table K.toAccepted where
  toFun := toAccepted
  invFun := ofAccepted
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem toAccepted_face (x : Cell K) (a : Bool) (n : ℕ) :
    (x.face a n).toAccepted = Thomason.DirectedComplex.Table.truncate n a x.toAccepted := by
  ext n a
  rfl

@[simp] theorem ofAccepted_truncate (x : Thomason.DirectedComplex.Table K.toAccepted)
    (n : ℕ) (a : Bool) :
    ofAccepted (Thomason.DirectedComplex.Table.truncate n a x) = (ofAccepted x).face a n := by
  ext a n
  rfl

@[simp] theorem toAccepted_comp (x y : Cell K) (n : ℕ)
    (h : x.face true n = y.face false n)
    (h' : Thomason.DirectedComplex.Table.truncate n true x.toAccepted =
      Thomason.DirectedComplex.Table.truncate n false y.toAccepted) :
    (Cell.comp x y n h).toAccepted =
      Thomason.DirectedComplex.Table.comp n x.toAccepted y.toAccepted h' := by
  ext n a
  rfl

@[simp] theorem toAccepted_map (f : Hom K L) (x : Cell K) :
    (Cell.map f x).toAccepted = f.toAccepted.table x.toAccepted := rfl

end Cell

/-- The two positive-table realizations are isomorphic as strict omega-categories. -/
def realizationIso (K : DirectedComplex.{u}) :
    toOmega.obj K.realization ≅ K.toAccepted.nu where
  hom :=
    { map := Cell.toAccepted
      map_source n x := Cell.toAccepted_face x false n
      map_target n x := Cell.toAccepted_face x true n
      map_comp n x y h h' := Cell.toAccepted_comp x y n h h' }
  inv :=
    { map := Cell.ofAccepted
      map_source n x := Cell.ofAccepted_truncate x n false
      map_target n x := Cell.ofAccepted_truncate x n true
      map_comp _ _ _ _ _ := by
        apply Cell.ext
        rfl }
  hom_inv_id := by
    apply Thomason.OmegaCategory.Functor.ext
    rfl
  inv_hom_id := by
    apply Thomason.OmegaCategory.Functor.ext
    rfl

/-- Realization of a positive chain map commutes with the presentation isomorphism. -/
theorem realizationIso_naturality {K L : DirectedComplex.{u}} (f : Hom K L) :
    toOmega.map f.realization ≫ (realizationIso L).hom =
      (realizationIso K).hom ≫ f.toAccepted.nu := by
  apply Thomason.OmegaCategory.Functor.ext
  rfl

end Thomason.Construction.DirectedComplex

end OAI
