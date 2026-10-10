import OAI.Algebra.AuslanderReiten.Homology.VectorCochainSplitting
import OAI.Algebra.AuslanderReiten.Homology.CochainNatTensorSigns
import OAI.Algebra.AuslanderReiten.Homology.BifunctorHomotopyEquiv
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products

namespace OAI

noncomputable section

namespace ArExplicit.VectorCochain

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

instance hasMapBifunctor (P Q : CochainComplex (ModuleCat.{u} k) ℕ) :
    HasMapBifunctor P Q F (ComplexShape.up ℕ) := fun _ => inferInstance

theorem totalMap_quasiIso {P P' Q Q' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : P ⟶ P') (g : Q ⟶ Q') [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g F (ComplexShape.up ℕ)) := by
  obtain ⟨e, rfl⟩ := (CochainComplex.quasiIso_iff_of_injective f).mp inferInstance
  obtain ⟨e', rfl⟩ := (CochainComplex.quasiIso_iff_of_injective g).mp inferInstance
  exact homotopyEquivalences_le_quasiIso _ _ _ ⟨totalHomotopyEquiv F e e', rfl⟩

theorem total_zero_differential (X Y : ℕ → ModuleCat.{u} k) (n m : ℕ) :
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ)).d n m = 0 := by
  rw [mapBifunctor.d_eq]
  have h₁ : mapBifunctor.D₁ (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ) n m = 0 := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [comp_zero, mapBifunctor.ι_D₁]
    rw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.up ℕ).Rel i (i+1) from rfl)]
    simp [zeroDifferential]
  have h₂ : mapBifunctor.D₂ (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ) n m = 0 := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [comp_zero, mapBifunctor.ι_D₂]
    rw [mapBifunctor.d₂_eq' _ _ _ _ i (show (ComplexShape.up ℕ).Rel j (j+1) from rfl)]
    simp [zeroDifferential]
  rw [h₁, h₂, add_zero]

def totalZeroHomologyIso (X Y : ℕ → ModuleCat.{u} k) (n : ℕ) :
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ)).homology n ≅
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ)).X n :=
  let K := mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (ComplexShape.up ℕ)
  (K.isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl
    (total_zero_differential k F X Y _ _)).symm ≪≫
  K.iCyclesIso n ((ComplexShape.up ℕ).next n) rfl (total_zero_differential k F X Y _ _)

variable (P Q : CochainComplex (ModuleCat.{u} k) ℕ)

def tensorSplitting :
    HomotopyEquiv
      (mapBifunctor (gradedHomology k P) (gradedHomology k Q) F (ComplexShape.up ℕ))
      (mapBifunctor P Q F (ComplexShape.up ℕ)) :=
  totalHomotopyEquiv F (splitting k P) (splitting k Q)

def kunnethIso (n : ℕ) :
    (mapBifunctor P Q F (ComplexShape.up ℕ)).homology n ≅
    (mapBifunctor (gradedHomology k P) (gradedHomology k Q) F (ComplexShape.up ℕ)).X n :=
  ((tensorSplitting k F P Q).toHomologyIso n).symm ≪≫
    totalZeroHomologyIso k F (fun i => P.homology i) (fun j => Q.homology j) n

theorem tensorSplitting_hom :
    (tensorSplitting k F P Q).hom =
      mapBifunctorMap (representatives k P) (representatives k Q) F (ComplexShape.up ℕ) := by
  simp [tensorSplitting, totalHomotopyEquiv]

theorem kunnethIso_inv (n : ℕ) :
    (kunnethIso k F P Q n).inv =
      (totalZeroHomologyIso k F (fun i => P.homology i) (fun j => Q.homology j) n).inv ≫
        homologyMap (mapBifunctorMap (representatives k P) (representatives k Q) F
          (ComplexShape.up ℕ)) n := by
  change _ ≫ homologyMap (tensorSplitting k F P Q).hom n = _
  rw [tensorSplitting_hom]

def kunnethLinearEquiv (n : ℕ) :
    (mapBifunctor P Q F (ComplexShape.up ℕ)).homology n ≃ₗ[k]
      (Π₀ p : {p : ℕ × ℕ // p.1 + p.2 = n},
        (F.obj (P.homology p.val.1)).obj (Q.homology p.val.2)) :=
  (kunnethIso k F P Q n).toLinearEquiv.trans
    (ModuleCat.coprodIsoDirectSum
      (fun p : {p : ℕ × ℕ // p.1 + p.2 = n} =>
        (F.obj (P.homology p.val.1)).obj (Q.homology p.val.2))).toLinearEquiv

end ArExplicit.VectorCochain

end

end OAI
