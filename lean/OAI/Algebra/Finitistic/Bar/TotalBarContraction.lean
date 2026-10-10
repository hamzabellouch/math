import OAI.Algebra.Finitistic.Bar.TotalBar
import OAI.Algebra.Finitistic.Bar.TotalAdditive

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
local instance (N : ModuleCat.{u} A) : Module k N := Module.compHom N (algebraMap k A)
local instance (N : ModuleCat.{u} A) : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (Z : ChainComplex (ModuleCat.{u} A) ℕ)
local notation "B" => barBicomplex k A Z
local notation "T" => barTotal k A Z
local notation "c" => ComplexShape.down ℕ
local notation "F" => moduleForgetAdd A

/-- Horizontal contribution with the declared total object as codomain. -/
def barTotalDH (i q n : ℕ) : (F).obj (((B).X i).X q) ⟶ (F).obj ((T).X n) :=
  (F).map ((B).d₁ c i q n)

/-- Vertical contribution with the declared total object as codomain. -/
def barTotalDV (i q n : ℕ) : (F).obj (((B).X i).X q) ⟶ (F).obj ((T).X n) :=
  (F).map ((B).d₂ c i q n)

/-- Unit insertion on an individual bar term, viewed as an additive map. -/
def barUnit (i q : ℕ) :
    AddCommGrpCat.of (term k A (Z.X q) i) ⟶ AddCommGrpCat.of (term k A (Z.X q) (i+1)) :=
  AddCommGrpCat.ofHom (contraction k A (Z.X q) i).toAddMonoidHom

/-- Unit insertion with the exact bicomplex source and target objects. -/
def barRaise (i q : ℕ) :
    (F).obj (((B).X i).X q) ⟶ (F).obj (((B).X (i+1)).X q) :=
  barUnit k A Z (i+1) q

/-- Natural unit insertion in the total bar, increasing bar length by one. -/
def barTotalH (n : ℕ) : (F).obj ((T).X n) ⟶ (F).obj ((T).X (n+1)) :=
  totalAddDesc B (fun i q h => barRaise k A Z i q ≫
    (F).map ((B).ιTotal c (i+1) q (n+1) (show i+1+q=n+1 by omega)))

@[reassoc (attr := simp)]
theorem ι_barTotalH (i q n : ℕ) (h : i+q=n) :
    (F).map ((B).ιTotal c i q n h) ≫ barTotalH k A Z n =
      barRaise k A Z i q ≫
        (F).map ((B).ιTotal c (i+1) q (n+1) (show i+1+q=n+1 by omega)) := by
  exact ι_totalAddDesc _ _ _ _ _

/-- Unit insertion in bar length zero gives the additive section. -/
def barTotalSectionF (n : ℕ) : (F).obj (Z.X n) ⟶ (F).obj ((T).X n) :=
  barUnit k A Z 0 n ≫ (F).map ((B).ιTotal c 0 n n (Nat.zero_add n))

@[reassoc (attr := simp)]
theorem barTotalSectionF_augmentation (n : ℕ) :
    barTotalSectionF k A Z n ≫ (F).map ((barTotalAugmentation k A Z).f n) = 𝟙 _ := by
  dsimp only [barTotal]
  dsimp only [barTotalSectionF, barTotalAugmentation]
  erw [Category.assoc, ← Functor.map_comp, ι_barTotalAugmentationF_zero]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  ext x
  exact contraction_zero k A (Z.X n) x

/-- Naturality of unit insertion under the input differential. -/
@[reassoc]
theorem barUnit_natural (i p q : ℕ) :
    (F).map (ModuleCat.ofHom (termMap k A (Z.X p) (Z.X q) (Z.d p q).hom i)) ≫
      barUnit k A Z i q =
    barUnit k A Z i p ≫
      (F).map (ModuleCat.ofHom (termMap k A (Z.X p) (Z.X q) (Z.d p q).hom (i+1))) := by
  ext x
  exact (contraction_natural k A (Z.X p) (Z.X q) (Z.d p q).hom i x).symm

/-- The additive section commutes with the input differential. -/
theorem barTotalSectionF_comm (n : ℕ) :
    barTotalSectionF k A Z (n+1) ≫ (F).map ((T).d (n+1) n) =
      (F).map (Z.d (n+1) n) ≫ barTotalSectionF k A Z n := by
  dsimp only [barTotal]
  dsimp only [barTotalSectionF]
  erw [Category.assoc, ← Functor.map_comp]
  simp only [barTotal, HomologicalComplex₂.total_d, comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    barTotal_d₁_zero, zero_add]
  erw [barTotal_d₂_succ k A Z 0 n n (by omega)]
  simp only [pow_zero, one_smul]
  erw [Functor.map_comp, ← Category.assoc, ← barUnit_natural]

/-- The row contraction identity, expressed in additive maps. -/
theorem barUnit_identity (i q : ℕ) :
    barUnit k A Z (i+1) q ≫ (F).map (ModuleCat.ofHom (differential k A (Z.X q) (i+1))) +
      (F).map (ModuleCat.ofHom (differential k A (Z.X q) i)) ≫ barUnit k A Z i q = 𝟙 _ := by
  ext x
  exact contraction_identity k A (Z.X q) i x

@[reassoc]
theorem ι_barTotal_d (i q n m : ℕ) (h : i+q=n) :
    (F).map ((B).ιTotal c i q n h) ≫ (F).map ((T).d n m) =
      barTotalDH k A Z i q m + barTotalDV k A Z i q m := by
  dsimp only [barTotal, barTotalDH, barTotalDV]
  erw [← Functor.map_comp]
  simp only [HomologicalComplex₂.total_d, comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, Functor.map_add]
  rfl

/-- The vertical contributions cancel because unit insertion changes bar parity. -/
theorem barTotal_vertical_cancel (i q n : ℕ) (h : i+q=n) :
    barTotalDV k A Z i (q+1) n ≫ barTotalH k A Z n +
      barRaise k A Z i (q+1) ≫ barTotalDV k A Z (i+1) (q+1) (n+1) = 0 := by
  dsimp only [barTotalDV]
  erw [barTotal_d₂_succ k A Z i q n h,
    barTotal_d₂_succ k A Z (i+1) q (n+1) (by omega)]
  erw [Functor.map_units_smul, Functor.map_units_smul,
    Functor.map_comp, Functor.map_comp, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc, ι_barTotalH]
  dsimp only [barRaise]
  erw [barUnit_natural_assoc]
  erw [pow_succ, mul_neg_one, Units.neg_smul, add_neg_cancel]

/-- Total contraction equation in degree zero. -/
theorem barTotalH_identity_zero :
    barTotalH k A Z 0 ≫ (F).map ((T).d 1 0) +
      (F).map ((barTotalAugmentation k A Z).f 0) ≫ barTotalSectionF k A Z 0 = 𝟙 _ := by
  dsimp only [barTotal]
  apply totalAdd_hom_ext B
  intro i q h
  have hi : i=0 := by omega
  have hq : q=0 := by omega
  subst i q
  erw [comp_add, ← Category.assoc, ι_barTotalH]
  erw [Category.assoc, ι_barTotal_d]
  dsimp only [barTotalDH, barTotalDV]
  erw [barTotal_d₁_succ k A Z 0 0 0 rfl, barTotal_d₂_zero]
  erw [Functor.map_zero, add_zero, Functor.map_comp]
  have ha : (F).map ((B).ιTotal c 0 0 0 h) ≫
      (F).map ((barTotalAugmentation k A Z).f 0) =
        (F).map (ModuleCat.ofHom (differential k A (Z.X 0) 0)) := by
    erw [← Functor.map_comp]
    change (F).map (_ ≫ barTotalAugmentationF k A Z 0) = _
    erw [ι_barTotalAugmentationF_zero]
    simp
    rfl
  erw [← Category.assoc ((F).map ((B).ιTotal c 0 0 0 h))
    ((F).map ((barTotalAugmentation k A Z).f 0)) (barTotalSectionF k A Z 0), ha]
  dsimp only [barTotalSectionF]
  erw [← Category.assoc]
  dsimp only [barRaise]
  erw [← Category.assoc, ← add_comp, barUnit_identity]
  ext x
  rfl

private theorem barTotal_horizontal_identity (n i q : ℕ) (h : i+q=n+1) :
    barTotalDH k A Z i q n ≫ barTotalH k A Z n +
      barRaise k A Z i q ≫ barTotalDH k A Z (i+1) q (n+1) +
      (F).map ((B).ιTotal c i q (n+1) h) ≫
        (F).map ((barTotalAugmentation k A Z).f (n+1)) ≫
          barTotalSectionF k A Z (n+1) = (F).map ((B).ιTotal c i q (n+1) h) := by
  dsimp only [barTotalDH]
  erw [barTotal_d₁_succ k A Z i q (n+1) h]
  cases i with
  | zero =>
    have hq : q=n+1 := by omega
    subst q
    erw [barTotal_d₁_zero, Functor.map_zero, zero_comp, zero_add,
      Functor.map_comp]
    dsimp only [barTotalAugmentation]
    erw [← Functor.map_comp_assoc (F) ((B).ιTotal c 0 (n+1) (n+1) h)
      (barTotalAugmentationF k A Z (n+1)) (barTotalSectionF k A Z (n+1))]
    erw [ι_barTotalAugmentationF_zero]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
    dsimp only [barTotalSectionF]
    erw [← Category.assoc]
    dsimp only [barRaise]
    erw [← Category.assoc, ← add_comp, barUnit_identity]
    ext x
    rfl
  | succ i =>
    erw [barTotal_d₁_succ k A Z i q n (by omega)]
    erw [Functor.map_comp, Functor.map_comp, Category.assoc,
      ι_barTotalH k A Z i q n (by omega)]
    dsimp only [barTotalAugmentation]
    erw [← Functor.map_comp_assoc (F) ((B).ιTotal c (i+1) q (n+1) h)
      (barTotalAugmentationF k A Z (n+1)) (barTotalSectionF k A Z (n+1))]
    erw [ι_barTotalAugmentationF_succ k A Z i q (n+1) h]
    erw [Functor.map_zero, zero_comp, add_zero, ← Category.assoc, ← Category.assoc]
    dsimp only [barRaise]
    erw [← add_comp]
    ext x
    exact congrArg ((F).map ((B).ιTotal c (i+1) q (n+1) h)).hom
      ((add_comm _ _).trans (contraction_identity k A (Z.X q) (i+1) x))

private theorem add_interleave {M : Type*} [AddCommMonoid M] (aa bb cc dd ee : M) :
    aa + bb + (cc + dd) + ee = (aa + cc + ee) + (bb + dd) := by
  abel

/-- Total contraction equation in every positive degree. -/
theorem barTotalH_identity_succ (n : ℕ) :
    (F).map ((T).d (n+1) n) ≫ barTotalH k A Z n +
      barTotalH k A Z (n+1) ≫ (F).map ((T).d (n+2) (n+1)) +
      (F).map ((barTotalAugmentation k A Z).f (n+1)) ≫
        barTotalSectionF k A Z (n+1) = 𝟙 _ := by
  dsimp only [barTotal]
  apply totalAdd_hom_ext B
  intro i q h
  have hv : barTotalDV k A Z i q n ≫ barTotalH k A Z n +
      barRaise k A Z i q ≫ barTotalDV k A Z (i+1) q (n+1) = 0 := by
    cases q with
    | zero =>
      dsimp only [barTotalDV]
      erw [barTotal_d₂_zero, barTotal_d₂_zero, Functor.map_zero,
        Functor.map_zero, zero_comp, comp_zero, add_zero]
    | succ q => exact barTotal_vertical_cancel k A Z i q n (by omega)
  have hh := barTotal_horizontal_identity k A Z n i q h
  erw [comp_add, comp_add, ← Category.assoc, ← Category.assoc,
    ι_barTotalH k A Z i q (n+1) h]
  erw [ι_barTotal_d, Category.assoc, ι_barTotal_d, add_comp, comp_add]
  calc
    _ = (barTotalDH k A Z i q n ≫ barTotalH k A Z n +
        barRaise k A Z i q ≫ barTotalDH k A Z (i+1) q (n+1) +
        (F).map ((B).ιTotal c i q (n+1) h) ≫
          (F).map ((barTotalAugmentation k A Z).f (n+1)) ≫
            barTotalSectionF k A Z (n+1)) +
      (barTotalDV k A Z i q n ≫ barTotalH k A Z n +
        barRaise k A Z i q ≫ barTotalDV k A Z (i+1) q (n+1)) :=
      add_interleave _ _ _ _ _
    _ = _ := by
      erw [hh, hv, add_zero]
      ext x
      rfl
end DerivedBar

end

end OAI
