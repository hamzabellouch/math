import OAI.Algebra.Finitistic.Selected.SelectedPDResidueProjection
import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryDimension
import OAI.Algebra.Finitistic.Dimension.PDResidueBaseBar
import OAI.Algebra.Finitistic.Selected.SelectedCountPDConsumer

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- Exact scalar/action-preserving identification with the source of the
bar worker's actual derived splitting. -/
def tensorBarDerivedIso (Y : FiniteSelectionFamily.S.{0}) :
    (DerivedBar.integerQ D).obj
      (DerivedBar.tensorBarComplex ℂ A D (Inflated Y) augmentation) ≅
        PDBarQuotient.baseDerived augmentation (Inflated Y) :=
  (DerivedBar.integerQ D).mapIso
    (DerivedBar.tensorBarIso ℂ A D (Inflated Y) augmentation)

/-- For the fixed actual A and Inflated Y, bounded actual D-bar homology
implies finite projective dimension, using the proved global dimension of D. -/
theorem finite_pd_of_bounded_base_bar (Y : FiniteSelectionFamily.S.{0})
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedBar.twoSidedComplex ℂ A D (Inflated Y) augmentation).homology n)) :
    projectiveDimension (module Y) < ⊤ :=
  PDResidueAssociativity.finite_pd_of_bounded_base_bar augmentation (Inflated Y)
    augmentation_surjective augmentation_kernel_square_zero
    SelectedOrdinaryDimension.bound SelectedOrdinaryDimension.left_module h

/-- Consumer of a supplied actual D-derived bar splitting with bounded target. -/
theorem finite_pd_of_base_derived_splitting (Y : FiniteSelectionFamily.S.{0})
    (Z : DerivedCategory (ModuleCat.{0} D))
    (e : PDBarQuotient.baseDerived augmentation (Inflated Y) ≅ Z)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj Z)) :
    projectiveDimension (module Y) < ⊤ :=
  PDResidueAssociativity.finite_pd_of_base_derived_iso augmentation (Inflated Y)
    augmentation_surjective augmentation_kernel_square_zero
    SelectedOrdinaryDimension.bound SelectedOrdinaryDimension.left_module Z e h

/-- Direct consumer whose source is literally the bar worker's integerQ value. -/
theorem finite_pd_of_tensor_bar_splitting (Y : FiniteSelectionFamily.S.{0})
    (Z : DerivedCategory (ModuleCat.{0} D))
    (e : (DerivedBar.integerQ D).obj
      (DerivedBar.tensorBarComplex ℂ A D (Inflated Y) augmentation) ≅ Z)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj Z)) :
    projectiveDimension (module Y) < ⊤ :=
  finite_pd_of_base_derived_splitting Y Z ((tensorBarDerivedIso Y).symm ≪≫ e) h

/-- The count retract can likewise be supplied at the bar worker's exact source. -/
theorem lower_bound_of_tensor_bar_count (Y : FiniteSelectionFamily.S.{0}) (r : ℕ)
    (h : ¬ IsZero (SelectedBaseIterates.object Y r))
    (i : SelectedCountCohomology.count Y r ⟶ (DerivedBar.integerQ D).obj
      (DerivedBar.tensorBarComplex ℂ A D (Inflated Y) augmentation))
    (p : (DerivedBar.integerQ D).obj
      (DerivedBar.tensorBarComplex ℂ A D (Inflated Y) augmentation) ⟶ SelectedCountCohomology.count Y r)
    (hip : i ≫ p = 𝟙 _) : r ≤ projectiveDimension (module Y) := by
  apply lower_bound_of_surviving_count Y r h (i ≫ (tensorBarDerivedIso Y).hom)
    ((tensorBarDerivedIso Y).inv ≫ p)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hip
end LittleFinitistic.SelectedPDDetection

end

end OAI
