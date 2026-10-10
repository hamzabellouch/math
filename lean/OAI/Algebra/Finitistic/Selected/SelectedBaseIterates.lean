import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryModules
import OAI.Algebra.Finitistic.Iteration.AdditiveIterateAmplitude

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedBaseIterates
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

/-- The actual first-block D-module underlying the inflated A-module. -/
abbrev input (Y : FiniteSelectionFamily.S.{0}) := ModuleCat.of D (Inflated Y)

local instance (N : ModuleCat.{0} D) : Module ℂ N := DerivedBar.BimoduleTensor.scalarModule ℂ D N
local instance (N : ModuleCat.{0} D) : IsScalarTower ℂ D N where
  smul_assoc c d n := by
    change (c • d) • n = (algebraMap ℂ D c) • (d • n)
    have hd : c • d = (algebraMap ℂ D c) * d := by
      exact Algebra.smul_def c d
    rw [hd, mul_smul]

instance input_finiteD (Y : FiniteSelectionFamily.S.{0}) : Module.Finite D (input Y) :=
  Module.Finite.of_restrictScalars_finite ℂ D (Inflated Y)

instance input_finite (Y : FiniteSelectionFamily.S.{0}) : FiniteDimensional ℂ (input Y) :=
  Module.Finite.trans D (input Y)

local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- Genuine bar-derived iteration of the actual X over the actual D. -/
abbrev object (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :=
  DerivedBar.IterateSupport.object ℂ D X (input Y) r

theorem cohomology_finite (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) (i : ℤ) :
    FiniteDimensional ℂ ((ModuleCat.restrictScalars (algebraMap ℂ D)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj (object Y r))) := by
  let : Module ℂ (input Y) := DerivedBar.BimoduleTensor.scalarModule ℂ D (input Y)
  have : IsScalarTower ℂ D (input Y) := by
    refine ⟨fun c d n => ?_⟩
    change (c • d) • n = (algebraMap ℂ D c) • (d • n)
    have hd : c • d = (algebraMap ℂ D c) * d := by exact Algebra.smul_def c d
    rw [hd, mul_smul]
  have : FiniteDimensional ℂ (input Y) := Module.Finite.trans D (input Y)
  exact DerivedBar.IterateSupport.cohomology_finite ℂ D X (input Y) r i

/-- A global-dimension bound on D bounds the amplitude of every derived iterate. -/
theorem bounded (g : ℕ) (hg : ∀ M : ModuleCat.{0} D, HasProjectiveDimensionLE M g)
    (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (object Y r).IsGE (-((r*(g+2) : ℕ) : ℤ)) ∧ (object Y r).IsLE 0 :=
  DerivedBar.IterateSupport.bounded_amplitude ℂ D X g hg (input Y) r
end LittleFinitistic.SelectedBaseIterates

end

end OAI
