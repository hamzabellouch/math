import OAI.Algebra.AuslanderReiten.Homology.VectorComplexSplitting
import OAI.Algebra.AuslanderReiten.Homology.BifunctorHomotopyEquiv
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products

namespace OAI

noncomputable section

namespace ArExplicit.VectorComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

instance hasMapBifunctor (P Q : ChainComplex (ModuleCat.{u} k) ℕ) :
    HasMapBifunctor P Q F (ComplexShape.down ℕ) := fun _ => inferInstance

theorem totalMap_quasiIso {P P' Q Q' : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : P ⟶ P') (g : Q ⟶ Q') [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g F (ComplexShape.down ℕ)) := by
  obtain ⟨e, rfl⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  obtain ⟨e', rfl⟩ := (ChainComplex.quasiIso_iff_of_projective g).mp inferInstance
  exact homotopyEquivalences_le_quasiIso _ _ _ ⟨totalHomotopyEquiv F e e', rfl⟩

theorem total_zero_differential (X Y : ℕ → ModuleCat.{u} k) (n m : ℕ) :
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.down ℕ)).d n m = 0 := by
  rw [mapBifunctor.d_eq]
  have h₁ : mapBifunctor.D₁ (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.down ℕ) n m = 0 := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [comp_zero, mapBifunctor.ι_D₁]
    cases i with
    | zero => exact mapBifunctor.d₁_eq_zero _ _ _ _ 0 j m (by simp)
    | succ i =>
      rw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.down ℕ).Rel (i+1) i from rfl)]
      simp [zeroDifferential]
  have h₂ : mapBifunctor.D₂ (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.down ℕ) n m = 0 := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [comp_zero, mapBifunctor.ι_D₂]
    cases j with
    | zero => exact mapBifunctor.d₂_eq_zero _ _ _ _ i 0 m (by simp)
    | succ j =>
      rw [mapBifunctor.d₂_eq' _ _ _ _ i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl)]
      simp [zeroDifferential]
  rw [h₁, h₂, add_zero]

def totalZeroHomologyIso (X Y : ℕ → ModuleCat.{u} k) (n : ℕ) :
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.down ℕ)).homology n ≅
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.down ℕ)).X n :=
  let K := mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (ComplexShape.down ℕ)
  (K.isoHomologyπ ((ComplexShape.down ℕ).prev n) n rfl
    (total_zero_differential k F X Y _ _)).symm ≪≫
  K.iCyclesIso n ((ComplexShape.down ℕ).next n) rfl (total_zero_differential k F X Y _ _)

variable (P Q : ChainComplex (ModuleCat.{u} k) ℕ)

def tensorSplitting :
    HomotopyEquiv
      (mapBifunctor (gradedHomology k P) (gradedHomology k Q) F (ComplexShape.down ℕ))
      (mapBifunctor P Q F (ComplexShape.down ℕ)) :=
  totalHomotopyEquiv F (splitting k P) (splitting k Q)

def kunnethIso (n : ℕ) :
    (mapBifunctor P Q F (ComplexShape.down ℕ)).homology n ≅
    (mapBifunctor (gradedHomology k P) (gradedHomology k Q) F (ComplexShape.down ℕ)).X n :=
  ((tensorSplitting k F P Q).toHomologyIso n).symm ≪≫
    totalZeroHomologyIso k F (fun i => P.homology i) (fun j => Q.homology j) n

theorem tensorSplitting_hom :
    (tensorSplitting k F P Q).hom =
      mapBifunctorMap (representatives k P) (representatives k Q) F (ComplexShape.down ℕ) := by
  simp [tensorSplitting, totalHomotopyEquiv]

theorem kunnethIso_inv (n : ℕ) :
    (kunnethIso k F P Q n).inv =
      (totalZeroHomologyIso k F (fun i => P.homology i) (fun j => Q.homology j) n).inv ≫
        homologyMap (mapBifunctorMap (representatives k P) (representatives k Q) F
          (ComplexShape.down ℕ)) n := by
  change _ ≫ homologyMap (tensorSplitting k F P Q).hom n = _
  rw [tensorSplitting_hom]

def kunnethLinearEquiv (n : ℕ) :
    (mapBifunctor P Q F (ComplexShape.down ℕ)).homology n ≃ₗ[k]
      (Π₀ p : {p : ℕ × ℕ // p.1 + p.2 = n},
        (F.obj (P.homology p.val.1)).obj (Q.homology p.val.2)) :=
  (kunnethIso k F P Q n).toLinearEquiv.trans
    (ModuleCat.coprodIsoDirectSum
      (fun p : {p : ℕ × ℕ // p.1 + p.2 = n} =>
        (F.obj (P.homology p.val.1)).obj (Q.homology p.val.2))).toLinearEquiv

end ArExplicit.VectorComplex

end

end OAI
