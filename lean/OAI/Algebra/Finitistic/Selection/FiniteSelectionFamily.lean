import OAI.Algebra.Finitistic.Selected.SelectedRealization

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.FiniteSelectionFamily
open SelectedFixedDiagram QuadraticEncoding

/-- Actual finite-dimensional modules over the fixed selecting algebra. -/
def S := {M : ModuleCat SelectionRing // FiniteDimensional ℂ (complexObject M)}
abbrev vector (Y : S) := complexObject Y.val
instance (Y : S) : FiniteDimensional ℂ (vector Y) := Y.property
instance ringModule (Y : S) : Module SelectionRing (vector Y) :=
  inferInstanceAs (Module SelectionRing Y.val)
instance tower (Y : S) : IsScalarTower ℂ SelectionRing (vector Y) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- H preserves this actual finite-dimensional family. -/
def H (Y : S) : S := ⟨selectionStep Y.val, by
  let : FiniteDimensional ℂ (complexObject Y.val) := Y.property
  exact selectionStep_finiteDimensional Y.val⟩

abbrev representation (Y : S) := SourceActionEvaluation.representation (Y := vector Y) encoding
abbrev module (Y : S) := EvaluationVertexDiagram.module (representation Y)
abbrev derived (Y : S) := (DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj (module Y)

/-- The proved one-step realization uses the actual endomap of the finite family. -/
def realization (Y : S) :
    SelectedTensorSplitting.object (representation Y).Evaluation ≅
      derived (H Y) ⊞ (derived (H Y))⟦(3 : ℤ)⟧ :=
  SelectedRealization.realization (Y := vector Y)

/-- Evaluation on three copies preserves and reflects the zero module. -/
theorem module_zero (Y : S) : IsZero (module Y) ↔ Subsingleton Y.val := by
  constructor
  · intro h
    let := ModuleCat.subsingleton_of_isZero h
    have inj : Function.Injective ((representation Y).inclusion 0) := by
      intro x y hxy
      have := congrArg ((representation Y).projection 0) hxy
      simpa only [Representation.projection_inclusion] using this
    exact inj.subsingleton
  · intro h
    let := h
    have : Subsingleton (representation Y).Evaluation :=
      inferInstanceAs (Subsingleton (Y.val × Y.val × Y.val))
    exact ModuleCat.isZero_of_subsingleton _

/-- The same exact zero criterion after embedding in the actual derived category. -/
theorem derived_zero (Y : S) : IsZero (derived Y) ↔ Subsingleton Y.val := by
  rw [← module_zero Y]
  constructor
  · intro h
    exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (B P)) 0).app
      (module Y)).isZero_iff.mp ((DerivedCategory.homologyFunctor (ModuleCat (B P)) 0).map_isZero h)
  · exact (DerivedCategory.singleFunctor (ModuleCat (B P)) 0).map_isZero

/-- Iteration is literally the Section 2 selection operation. -/
theorem iterate_val (j : ℕ) (Y : S) : ((H^[j]) Y).val = selectionIterate Y.val j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change selectionStep ((H^[j]) Y).val = selectionStep (selectionIterate Y.val j)
    exact congrArg selectionStep ih

def test (m : ℕ) [NeZero m] : S := ⟨testObject m, testObject_finiteDimensional m⟩

/-- Exact finite extinction is retained by the actual derived evaluation family. -/
theorem extinction (m : ℕ) [NeZero m] :
    (∀ j < m, ¬ IsZero (derived ((H^[j]) (test m)))) ∧
      IsZero (derived ((H^[m]) (test m))) := by
  constructor
  · intro j hj hz
    have hs := (derived_zero _).mp hz
    rw [iterate_val] at hs
    have hn := selectionIterate_test_nontrivial m j hj
    exact @not_subsingleton _ hn hs
  · apply (derived_zero _).mpr
    rw [iterate_val]
    exact selectionIterate_test_subsingleton m
end LittleFinitistic.FiniteSelectionFamily

end

end OAI
