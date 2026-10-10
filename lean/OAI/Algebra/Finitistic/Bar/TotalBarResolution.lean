import OAI.Algebra.Finitistic.Bar.TotalBarContraction
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Z : ChainComplex (ModuleCat.{u} A) ℕ)
local notation "c" => ComplexShape.down ℕ
local notation "F" => moduleForgetAdd A
local notation "P" => CategoryTheory.Functor.obj
  (CategoryTheory.Functor.mapHomologicalComplex (moduleForgetAdd A) (ComplexShape.down ℕ)) (barTotal k A Z)
local notation "Q" => CategoryTheory.Functor.obj
  (CategoryTheory.Functor.mapHomologicalComplex (moduleForgetAdd A) (ComplexShape.down ℕ)) Z
local notation "π" => CategoryTheory.Functor.map
  (CategoryTheory.Functor.mapHomologicalComplex (moduleForgetAdd A) (ComplexShape.down ℕ)) (barTotalAugmentation k A Z)

/-- Unit insertion is an actual additive chain section of the total augmentation. -/
def barTotalSection : Q ⟶ P where
  f := barTotalSectionF k A Z
  comm' i j h := by
    change j+1=i at h
    subst i
    exact barTotalSectionF_comm k A Z j

/-- The explicit additive contraction, with its degree condition. -/
def barTotalHomotopy : Homotopy (𝟙 P) (π ≫ barTotalSection k A Z) where
  hom i j := if h : i+1=j then barTotalH k A Z i ≫ ((P).XIsoOfEq h).hom else 0
  zero i j h := by
    change ¬ i+1=j at h
    exact dite_eq_right h
  comm i := by
    rw [prevD_eq _ (by rfl : (c).Rel (i+1) i)]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    cases i with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp), zero_add]
      exact (barTotalH_identity_zero k A Z).symm
    | succ n =>
      rw [dNext_eq _ (by rfl : (c).Rel (n+1) n)]
      simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
      exact (barTotalH_identity_succ k A Z n).symm

/-- The total augmentation is a homotopy equivalence after forgetting the A-action.
The inverse and homotopy are explicit unit insertions, not A-linear splittings. -/
def barTotalAdditiveEquiv : HomotopyEquiv P Q where
  hom := π
  inv := barTotalSection k A Z
  homotopyHomInvId := (barTotalHomotopy k A Z).symm
  homotopyInvHomId := Homotopy.ofEq (by
    apply HomologicalComplex.Hom.ext
    funext n
    exact barTotalSectionF_augmentation k A Z n)

/-- The actual D-linear total-bar augmentation is a quasi-isomorphism for every
nonnegative chain input; neither projectivity nor flatness of the input is assumed. -/
instance barTotalAugmentation_quasiIso : QuasiIso (barTotalAugmentation k A Z) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (barTotalAugmentation k A Z) (moduleForgetAdd A)]
  exact (barTotalAdditiveEquiv k A Z).quasiIso_hom

/-- The source's bounded-above cochain model is obtained by the literal n ↦ -n extension. -/
def barTotalCochain : CochainComplex (ModuleCat.{u} A) ℤ :=
  (barTotal k A Z).extend ComplexShape.embeddingDownNat

/-- The proved projective total terms make the cochain extension K-projective. -/
instance barTotalCochain_isKProjective : (barTotalCochain k A Z).IsKProjective := by
  let : ∀ n, Projective ((barTotal k A Z).X n) := barTotal_projective k A Z
  exact inferInstanceAs (CochainComplex.IsKProjective ((barTotal k A Z).extend ComplexShape.embeddingDownNat))
end DerivedBar

end

end OAI
