import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryAlgebra
import OAI.Algebra.Finitistic.Selection.FiniteSelectionFamily

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedOrdinaryModules
open SelectedFixedDiagram QuadraticEncoding SelectedOrdinaryAlgebra
open FiniteSelectionFamily

/-- The source module M(Y), supported on the first D-block and inflated to A. -/
def Inflated (Y : S.{0}) := (representation Y).Evaluation
instance (Y : S.{0}) : AddCommGroup (Inflated Y) :=
  inferInstanceAs (AddCommGroup (representation Y).Evaluation)
instance (Y : S.{0}) : Module ℂ (Inflated Y) :=
  inferInstanceAs (Module ℂ (representation Y).Evaluation)
instance (Y : S.{0}) : Module (B P) (Inflated Y) :=
  inferInstanceAs (Module (B P) (representation Y).Evaluation)
instance (Y : S.{0}) : IsScalarTower ℂ (B P) (Inflated Y) :=
  inferInstanceAs (IsScalarTower ℂ (B P) (representation Y).Evaluation)

abbrev firstProjection : D →+* B P := RingHom.fst _ _
abbrev augmentationRing : A →+* D := SelectedOrdinaryAlgebra.augmentation.toRingHom
instance (Y : S.{0}) : Module D (Inflated Y) := Module.compHom (Inflated Y) firstProjection
instance (Y : S.{0}) : Module A (Inflated Y) :=
  Module.compHom (Inflated Y) (firstProjection.comp augmentationRing)
instance (Y : S.{0}) : IsScalarTower ℂ D (Inflated Y) where
  smul_assoc c d x := by
    change (c • d.1) • x = c • (d.1 • x)
    exact smul_assoc c d.1 x
instance (Y : S.{0}) : IsScalarTower ℂ A (Inflated Y) where
  smul_assoc c a x := by
    change (c • a.fst.1) • x = c • (a.fst.1 • x)
    exact smul_assoc c a.fst.1 x
instance (Y : S.{0}) : FiniteDimensional ℂ (Inflated Y) :=
  inferInstanceAs (FiniteDimensional ℂ (representation Y).Evaluation)

instance (Y : S.{0}) : Module.Finite A (Inflated Y) :=
  Module.Finite.of_restrictScalars_finite ℂ A (Inflated Y)

abbrev module (Y : S.{0}) := ModuleCat.of A (Inflated Y)

/-- The actual D-action is exactly the original first B-block action. -/
theorem first_action (Y : S.{0}) (d : D) (n : Inflated Y) : d • n = d.1 • n := rfl
/-- The square-zero ideal acts by zero, as required by the bar calculation. -/
theorem ideal_annihilates (Y : S.{0}) (x : X) (n : Inflated Y) :
    (TrivSqZeroExt.inr x : A) • n = 0 := by
  change (0 : B P) • n = 0
  exact zero_smul _ _
theorem base_action (Y : S.{0}) (d : D) (n : Inflated Y) :
    (TrivSqZeroExt.inl d : A) • n = d • n := rfl

/-- Inflation preserves exactly the original module's zero criterion. -/
theorem isZero_iff (Y : S.{0}) : IsZero (module Y) ↔ Subsingleton Y.val := by
  rw [← FiniteSelectionFamily.module_zero Y]
  change IsZero (ModuleCat.of A (Inflated Y)) ↔ IsZero (FiniteSelectionFamily.module Y)
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

/-- Actual finite-dimensional modules over the one fixed A; their projective
 dimensions are the remaining homological conclusion. -/
abbrev testModule (m : ℕ) [NeZero m] := module (test m)

theorem test_nonzero (m : ℕ) [NeZero m] : ¬ IsZero (testModule m) := by
  intro h
  have hs := (isZero_iff (test m)).mp h
  have hn := selectionIterate_test_nontrivial m 0 (NeZero.pos m)
  exact @not_subsingleton _ hn hs
end LittleFinitistic.SelectedOrdinaryModules

end

end OAI
