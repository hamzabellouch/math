import OAI.Algebra.Finitistic.Selected.SelectedPDDetection
import OAI.Algebra.Finitistic.Dimension.PDBaseBarConsumer

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

/-- The literal two-sided bar over the one fixed square-zero algebra. -/
abbrev baseBar (Y : FiniteSelectionFamily.S.{0}) :=
  DerivedBar.twoSidedComplex ℂ A D (Inflated Y) augmentation

/-- Actual Tor at the native bar model, using the canonical augmentation. -/
def torIsoBaseBar (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    PDTensor.Tor (k := ℂ) (PDBarQuotient.RightBase augmentation) (module Y) n ≅
      (((ModuleCat.restrictScalars (algebraMap ℂ D)).mapHomologicalComplex _).obj
        (baseBar Y)).homology n :=
  PDBarQuotient.torIsoTwoSided augmentation (Inflated Y) n

theorem lower_bound_of_base_bar (Y : FiniteSelectionFamily.S.{0})
    (r n : ℕ) (hrn : r ≤ n) (h : ¬ IsZero ((baseBar Y).homology n)) :
    r ≤ projectiveDimension (module Y) :=
  PDBarQuotient.lower_bound_of_base_bar augmentation (Inflated Y) r n hrn h

local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- Native supplies its actual D-linear derived splitting and the surviving
summand's cohomology. The detector constructs the projective-dimension bound. -/
theorem lower_bound_of_base_derived_bar (Y : FiniteSelectionFamily.S.{0})
    (Z T : DerivedCategory (ModuleCat.{0} D))
    (e : PDBarQuotient.baseDerived augmentation (Inflated Y) ≅ Z)
    (i : T ⟶ Z) (p : Z ⟶ T) (hip : i ≫ p = 𝟙 T)
    (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj T)) :
    r ≤ projectiveDimension (module Y) :=
  PDBarQuotient.lower_bound_of_base_derived_retract augmentation (Inflated Y)
    Z T e i p hip r n hrn h
end LittleFinitistic.SelectedPDDetection

end

end OAI
