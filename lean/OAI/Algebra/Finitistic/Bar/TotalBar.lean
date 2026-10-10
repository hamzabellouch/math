import OAI.Algebra.Finitistic.Bar.BarFunctor
import Mathlib.Algebra.Homology.Homotopy

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
local instance (N : ModuleCat.{u} A) : Module k N := Module.compHom N (algebraMap k A)
local instance (N : ModuleCat.{u} A) : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Total terms are projective for every nonnegative input, without projectivity
or flatness assumptions on the input terms. -/
instance barTotal_projective (Z : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    Projective ((barTotal k A Z).X n) where
  factors f e he := by
    dsimp only [barTotal] at f ⊢
    refine ⟨(barBicomplex k A Z).totalDesc
      (fun i q h => Projective.factorThru
        ((barBicomplex k A Z).ιTotal _ i q n h ≫ f) e), ?_⟩
    apply HomologicalComplex₂.total.hom_ext
    intro i q h
    simp

variable (Z : ChainComplex (ModuleCat.{u} A) ℕ)
local notation "B" => barBicomplex k A Z
local notation "T" => barTotal k A Z
local notation "c" => ComplexShape.down ℕ

/-- The augmentation is the action in bar length zero and zero elsewhere. -/
def barTotalAugmentationF (n : ℕ) : (T).X n ⟶ Z.X n :=
  (B).totalDesc (fun i q h => match i with
    | 0 => ModuleCat.ofHom (differential k A (Z.X q) 0) ≫
        (Z.XIsoOfEq (by simpa using h)).hom
    | _+1 => 0)

@[reassoc (attr := simp)]
theorem ι_barTotalAugmentationF_zero (q n : ℕ) (h : 0 + q = n) :
    (B).ιTotal c 0 q n h ≫ barTotalAugmentationF k A Z n =
      ModuleCat.ofHom (differential k A (Z.X q) 0) ≫
        (Z.XIsoOfEq (by omega : q = n)).hom := by
  apply HomologicalComplex₂.ι_totalDesc

@[reassoc (attr := simp)]
theorem ι_barTotalAugmentationF_succ (i q n : ℕ) (h : i+1+q=n) :
    (B).ιTotal c (i+1) q n h ≫ barTotalAugmentationF k A Z n = 0 := by
  apply HomologicalComplex₂.ι_totalDesc

/-- Horizontal face formula in positive bar length. -/
theorem barTotal_d₁_succ (i q n : ℕ) (h : i+q=n) :
    (B).d₁ c (i+1) q n =
      ModuleCat.ofHom (differential k A (Z.X q) (i+1)) ≫ (B).ιTotal c i q n h := by
  rw [HomologicalComplex₂.d₁_eq _ _ (by rfl : (c).Rel (i+1) i) q n h]
  change (1 : ℤˣ) • ((complex k A (Z.X q)).d (i+1) i ≫ _) = _
  erw [one_smul]
  simp only [complex, ChainComplex.of_d]

/-- The horizontal differential is absent in bar length zero. -/
@[simp] theorem barTotal_d₁_zero (q n : ℕ) : (B).d₁ c 0 q n = 0 := by
  apply HomologicalComplex₂.d₁_eq_zero
  simp

/-- The vertical differential is absent in input degree zero. -/
@[simp] theorem barTotal_d₂_zero (i n : ℕ) : (B).d₂ c i 0 n = 0 := by
  apply HomologicalComplex₂.d₂_eq_zero
  simp

/-- Vertical face formula, with the standard totalization sign. -/
theorem barTotal_d₂_succ (i q n : ℕ) (h : i+q=n) :
    (B).d₂ c i (q+1) n =
      ((-1 : ℤˣ)^i) • (ModuleCat.ofHom
        (termMap k A (Z.X (q+1)) (Z.X q) (Z.d (q+1) q).hom (i+1)) ≫
          (B).ιTotal c i q n h) := by
  rw [HomologicalComplex₂.d₂_eq _ _ i (by rfl : (c).Rel (q+1) q) n h]
  rfl

/-- The total augmentation is a chain map. -/
theorem barTotalAugmentation_comm (n : ℕ) :
    (T).d (n+1) n ≫ barTotalAugmentationF k A Z n =
      barTotalAugmentationF k A Z (n+1) ≫ Z.d (n+1) n := by
  apply HomologicalComplex₂.total.hom_ext
  intro i q h
  change i+q=n+1 at h
  simp only [barTotal, HomologicalComplex₂.total_d]
  erw [add_comp, comp_add, HomologicalComplex₂.ι_D₁_assoc,
    HomologicalComplex₂.ι_D₂_assoc]
  cases i with
  | zero =>
    have hq : q=n+1 := by omega
    subst q
    erw [barTotal_d₁_zero, zero_comp, zero_add,
      barTotal_d₂_succ k A Z 0 n n (by omega)]
    erw [pow_zero, one_smul, Category.assoc, ι_barTotalAugmentationF_zero,
      ι_barTotalAugmentationF_zero_assoc]
    simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, Category.comp_id]
    apply ModuleCat.hom_ext
    exact differential_natural k A (Z.X (n+1)) (Z.X n) (Z.d (n+1) n).hom 0
  | succ i =>
    erw [barTotal_d₁_succ k A Z i q n (by omega)]
    erw [Category.assoc]
    erw [ι_barTotalAugmentationF_succ_assoc k A Z i q (n+1) h]
    erw [zero_comp]
    have hhor : ModuleCat.ofHom (differential k A (Z.X q) (i+1)) ≫
        (B).ιTotal c i q n (show i+q=n by omega) ≫ barTotalAugmentationF k A Z n = 0 := by
      cases i with
      | zero =>
        have hn : q=n := by omega
        subst n
        erw [ι_barTotalAugmentationF_zero]
        simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl,
          Iso.refl_hom, Category.comp_id]
        exact ModuleCat.hom_ext (differential_sq k A (Z.X q) 0)
      | succ i => erw [ι_barTotalAugmentationF_succ, comp_zero]
    erw [hhor, zero_add]
    cases q with
    | zero => erw [barTotal_d₂_zero, zero_comp]
    | succ q =>
      erw [barTotal_d₂_succ k A Z (i+1) q n (by omega)]
      erw [CategoryTheory.Linear.units_smul_comp, Category.assoc,
        ι_barTotalAugmentationF_succ, comp_zero, smul_zero]

def barTotalAugmentation : T ⟶ Z where
  f := barTotalAugmentationF k A Z
  comm' i j h := by
    change j+1=i at h
    subst i
    exact (barTotalAugmentation_comm k A Z j).symm
end DerivedBar

end

end OAI
