import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.PowerDiagonal
import OAI.GroupTheory.SimpleAmenable.Homology.StageRefinementHomology
import OAI.GroupTheory.SimpleAmenable.Configurations.EmptyStage

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace BarFinitePower
variable (κ:Type) (X:SSet)
def evaluate (k:κ) : (power κ).obj X ⟶ X where
  app _ := ↾fun x => x k
  naturality _ _ _ := rfl
lemma lift_evaluate {Y:SSet} (f:κ → (Y ⟶ X)) (k:κ) : lift κ f ≫ evaluate κ X k=f k := rfl
end BarFinitePower
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower UniformObject

variable {a n:ℕ} {S T:Stage a n} (h:S≤T)
    (c:Fin T.partition.size × Fin T.support.card)
noncomputable def newLabelIso (hc:∀j,S.L j ≠ T.L c.2) :
    FiniteSetGroupoid.terminal ⋙ FiniteSetGroupoid.emptyFunctor ≅
      inclusion h ⋙ evaluation (P:=T.partition) (L:=T.L) ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (C := FiniteSetGroupoid)
    (X := FiniteSetGroupoid.empty) (Y := E.obj ((inclusion h).obj U) c)
    (show FiniteSetGroupoid.empty ⟶ E.obj ((inclusion h).obj U) c from
    finCongr (new_label_size h c hc U).symm)) (by
      intros; apply Equiv.ext; intro x; exact Fin.elim0 x)
noncomputable instance newLabelIsoMonoidal (hc:∀j,S.L j ≠ T.L c.2) :
    NatTrans.IsMonoidal (newLabelIso h c hc).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor _ _ := by apply Equiv.ext; intro x; exact Fin.elim0 x
lemma newLabel_homology_zero (hc:∀j,S.L j ≠ T.L c.2) (j:ℕ) (hj:0<j) :
    SSet.homologyMap (bar₃Map (inclusion h ⋙ evaluation (P:=T.partition) (L:=T.L) ⋙ project _ c))
      DiagonalResolution.Z j=0 := by
  rw [←bar₃Map_eq_of_monoidalNatTrans (newLabelIso h c hc).hom j,
    bar₃Map_comp,SSet.homologyMap_comp]
  have hz := bar₃_acyclic (C:=FiniteSetGroupoid.Terminal) (fun x y => ⟨eqToHom (Subsingleton.elim x y)⟩) j hj
  rw [hz.eq_of_src (SSet.homologyMap (bar₃Map FiniteSetGroupoid.emptyFunctor) DiagonalResolution.Z j) 0,Limits.comp_zero]
variable (S)
lemma finiteProductComparison_coordinate
    (b:Fin S.partition.size × Fin S.support.card) :
    S.finiteProductComparison ≫ evaluate _ _ b =
      bar₃Map (evaluation (P:=S.partition) (L:=S.L) ⋙ project _ b) := by
  rw [finiteProductComparison,Category.assoc]
  change bar₃Map UniformObject.evaluation ≫ bar₃Map (project _ b) = _
  rw [←bar₃Map_comp]
variable {S}
lemma refinement_coordinate
    (b:Fin S.partition.size × Fin S.support.card)
    (hp:S.partition.color (T.partition.point c.1)=b.1)
    (hl:S.L b.2=T.L c.2) (j:ℕ) :
    SSet.homologyMap (S.finiteProductComparison ≫ evaluate _ _ b) DiagonalResolution.Z j =
      SSet.homologyMap (bar₃Map (inclusion h) ≫ T.finiteProductComparison ≫ evaluate _ _ c)
        DiagonalResolution.Z j := by
  rw [finiteProductComparison_coordinate,finiteProductComparison_coordinate,←bar₃Map_comp]
  exact refinement_coordinate_homology h b c hp hl j
lemma refinement_new_label_zero (hc:∀j,S.L j ≠ T.L c.2) (j:ℕ) (hj:0<j) :
    SSet.homologyMap (bar₃Map (inclusion h) ≫ T.finiteProductComparison ≫ evaluate _ _ c)
      DiagonalResolution.Z j=0 := by
  rw [finiteProductComparison_coordinate,←bar₃Map_comp]
  exact newLabel_homology_zero h c hc j hj
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower

variable (X:SSet)
noncomputable def reindexIso {κ ι:Type} (e:κ≃ι) : (power κ).obj X ≅ (power ι).obj X where
  hom := { app _ := ↾fun x i => x (e.symm i)
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun x k => x (e k)
           naturality _ _ _ := rfl }
  hom_inv_id := by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext k; exact congrArg x (e.symm_apply_apply k)
  inv_hom_id := by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i; exact congrArg x (e.apply_symm_apply i)
noncomputable def finSuccIso (s:ℕ) : (power (Fin (s+1))).obj X ≅ X ⊗ (power (Fin s)).obj X where
  hom := { app _ := ↾fun x => (x 0,fun i => x i.succ)
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun x => Fin.cases x.1 x.2
           naturality _ _ _ := by
             apply ConcreteCategory.hom_ext; intro x; funext i
             cases i using Fin.cases <;> rfl }
  hom_inv_id := by
    apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i
    cases i using Fin.cases <;> rfl
  inv_hom_id := by ext p x <;> rfl
noncomputable def finZeroIso : (power (Fin 0)).obj X ≅ ConnectedProduct.one where
  hom := { app _ := ↾fun _ => PUnit.unit
           naturality _ _ _ := rfl }
  inv :=
    { app _ := ↾fun _ => Fin.elim0
      naturality _ _ _ := by apply ConcreteCategory.hom_ext; intro x; funext i; exact i.elim0 }
  hom_inv_id := by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i; exact i.elim0
  inv_hom_id := by ext p x; rfl
lemma connected_of_iso {Y:SSet} (e:X≅Y) [Y.IsConnected] : X.IsConnected where
  allEq x y := by
    have he := congrArg (SSet.mapπ₀ e.inv) (Subsingleton.elim (SSet.mapπ₀ e.hom x) (SSet.mapπ₀ e.hom y))
    simpa only [←SSet.mapπ₀_comp_apply,Iso.hom_inv_id,SSet.mapπ₀_id_apply] using he
  nonempty := ⟨e.inv.app _ (Classical.arbitrary _)⟩
instance connected_one : ConnectedProduct.one.IsConnected where
  allEq x y := by
    obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective x
    obtain ⟨y,rfl⟩ := SSet.π₀.mk_surjective y
    exact congrArg SSet.π₀.mk (show x=y from PUnit.ext x y)
  nonempty := ⟨PUnit.unit⟩
lemma fin_connected [X.IsConnected] (s:ℕ) : ((power (Fin s)).obj X).IsConnected := by
  induction s with
  | zero => exact connected_of_iso _ (finZeroIso X)
  | succ s ih =>
    have connectedPower := ih
    exact connected_of_iso _ (finSuccIso X s)
noncomputable instance connected (κ:Type) [Finite κ] [X.IsConnected] : ((power κ).obj X).IsConnected := by
  let finiteCoordinates := Fintype.ofFinite κ
  have connectedPower := fin_connected X (Fintype.card κ)
  exact connected_of_iso _ (reindexIso X (Fintype.equivFin κ))
lemma homology_zero_finite [X.IsConnected] : Module.Finite ℤ (X.homology DiagonalResolution.Z 0 : FreeChains.A) :=
  Module.Finite.equiv (asIso (X.homology₀ε DiagonalResolution.Z)).symm.toLinearEquiv
lemma homology_isZero_complex (q:ℕ) (h:IsZero (X.homology DiagonalResolution.Z q)) :
    IsZero ((FreeChains.complex X).homology q) :=
  IsZero.of_iso h ((HomologicalComplex.homologyFunctor FreeChains.A FreeChains.c q).mapIso (FreeChains.complexIso X)).symm
lemma homology_finite_complex (q:ℕ) [Module.Finite ℤ (X.homology DiagonalResolution.Z q : FreeChains.A)] :
    Module.Finite ℤ ((FreeChains.complex X).homology q) := by
  have finiteHomology : Module.Finite ℤ ((X.chainComplex FreeChains.Z).homology q : FreeChains.A) := ‹Module.Finite ℤ (X.homology DiagonalResolution.Z q : FreeChains.A)›
  exact (Module.Finite.equiv_iff ((HomologicalComplex.homologyFunctor FreeChains.A FreeChains.c q).mapIso (FreeChains.complexIso X)).toLinearEquiv).mp ‹Module.Finite ℤ ((X.chainComplex FreeChains.Z).homology q : FreeChains.A)›
end BarFinitePower

end

end

end OAI
