import OAI.Algebra.Finitistic.Dimension.PDResidueScalar
import OAI.Algebra.Finitistic.Selected.SelectedBarResolution
import OAI.Algebra.Finitistic.Selected.SelectedMinimalResolution
import OAI.Algebra.Finitistic.Dimension.PDBarDetection
import OAI.Algebra.Finitistic.Dimension.PDDerivedBarConsumer
import OAI.Algebra.Finitistic.Dimension.PDSquareZeroResidue

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

instance residueModuleK : Module ℂ (PDTensor.Residue (A := A)) := PDResidueScalar.moduleK ℂ A
instance residueTowerK : IsScalarTower ℂ Aᵐᵒᵖ (PDTensor.Residue (A := A)) := PDResidueScalar.towerK ℂ A

open SelectedMinimalResolution (finiteModule)

abbrev barTensor (Y : FiniteSelectionFamily.S.{0})
    (U : Type) [AddCommGroup U] [Module ℂ U] [Module Aᵐᵒᵖ U] :=
  PDBar.tensorComplex (finiteModule Y) U (SelectedBarResolution.resolution Y)

def torIsoBar (Y : FiniteSelectionFamily.S.{0})
    (U : Type) [AddCommGroup U] [Module ℂ U] [Module Aᵐᵒᵖ U] (n : ℕ) :
    PDTensor.Tor (k := ℂ) U (module Y) n ≅ (barTensor Y U).homology n :=
  PDBar.torIsoResolution (finiteModule Y) U (SelectedBarResolution.resolution Y) n

theorem pdLE_iff_residue_bar (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    HasProjectiveDimensionLE (module Y) n ↔
      IsZero ((barTensor Y (PDTensor.Residue (A := A))).homology (n+1)) :=
  PDBar.pdLE_iff_residue_resolution (finiteModule Y) (SelectedBarResolution.resolution Y) n

theorem pdLE_iff_simple_bar (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    HasProjectiveDimensionLE (module Y) n ↔
      ∀ S : Submodule Aᵐᵒᵖ (PDTensor.Residue (A := A)), IsSimpleModule Aᵐᵒᵖ S →
        IsZero ((barTensor Y S).homology (n+1)) :=
  PDBar.pdLE_iff_simple_resolution (finiteModule Y) (SelectedBarResolution.resolution Y) n

theorem finite_pd_of_bar (Y : FiniteSelectionFamily.S.{0})
    (h : ∃ b : ℕ, ∀ n, b < n →
      IsZero ((barTensor Y (PDTensor.Residue (A := A))).homology n)) :
    projectiveDimension (module Y) < ⊤ :=
  PDTensor.finite_pd_of_resolution (finiteModule Y) (SelectedBarResolution.resolution Y) h

theorem lower_bound_of_bar (Y : FiniteSelectionFamily.S.{0})
    (U : Type) [AddCommGroup U] [Module ℂ U] [Module Aᵐᵒᵖ U]
    (r n : ℕ) (hrn : r ≤ n) (h : ¬ IsZero ((barTensor Y U).homology n)) :
    r ≤ projectiveDimension (module Y) :=
  PDTensor.lower_bound_of_resolution (finiteModule Y) U
    (SelectedBarResolution.resolution Y) r n hrn h

local instance : HasDerivedCategory.{1} (ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard (ModuleCat.{0} ℂ)

theorem finite_pd_of_derived_bar (Y : FiniteSelectionFamily.S.{0})
    (Z : DerivedCategory (ModuleCat.{0} ℂ))
    (e : PDBar.derivedObject (barTensor Y (PDTensor.Residue (A := A))) ≅ Z)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat ℂ) (-(n : ℤ))).obj Z)) :
    projectiveDimension (module Y) < ⊤ :=
  PDBar.finite_pd_of_derived_iso (finiteModule Y) (SelectedBarResolution.resolution Y) Z e h

theorem lower_bound_of_derived_bar (Y : FiniteSelectionFamily.S.{0})
    (U : Type) [AddCommGroup U] [Module ℂ U] [Module Aᵐᵒᵖ U]
    (Z T : DerivedCategory (ModuleCat.{0} ℂ))
    (e : PDBar.derivedObject (barTensor Y U) ≅ Z)
    (i : T ⟶ Z) (p : Z ⟶ T) (hip : i ≫ p = 𝟙 T)
    (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat ℂ) (-(n : ℤ))).obj T)) :
    r ≤ projectiveDimension (module Y) :=
  PDBar.lower_bound_of_derived_retract (finiteModule Y) (SelectedBarResolution.resolution Y)
    U Z T e i p hip r n hrn h
end LittleFinitistic.SelectedPDDetection

end

end OAI
