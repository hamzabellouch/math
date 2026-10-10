import OAI.Algebra.Finitistic.Selection.FiniteSelectionFamily
import OAI.Algebra.Finitistic.Iteration.ObjectwiseSplitting

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedIteration
open SelectedFixedDiagram QuadraticEncoding FiniteSelectionFamily

variable (Phi : DerivedCategory (ModuleCat (B P)) ⥤ DerivedCategory (ModuleCat (B P)))
  [Phi.Additive] [Phi.CommShift ℤ]
/- This is solely the remaining derived-tensor/stalk comparison. The realization
and exact reference cohomology have already been proved independently. -/
variable (comparison : ∀ Y : S, Phi.obj (derived Y) ≅
  SelectedTensorSplitting.object (representation Y).Evaluation)
include comparison

def split (Y : S) : Phi.obj (derived Y) ≅ derived (H Y) ⊞ (derived (H Y))⟦(3 : ℤ)⟧ :=
  comparison Y ≪≫ FiniteSelectionFamily.realization Y

/-- The exact binomial formula, instantiated with the actual finite module family. -/
def iteration (j : ℕ) (Y : S) :
    (Phi.obj^[j]) (derived Y) ≅
      ⨁ fun q : Fin (j+1) => ⨁ fun _ : Fin (Nat.choose j q.val) =>
        (derived ((H^[j]) Y))⟦(3 : ℤ)*(q.val : ℤ)⟧ :=
  ExternalTensor.Binomial.section4Iteration Phi derived H (split Phi comparison) j Y

private def shiftedSplit (Y : S) :
    Phi.obj (derived Y) ≅ (derived (H Y))⟦(0 : ℤ)⟧ ⊞ (derived (H Y))⟦(0+3 : ℤ)⟧ :=
  split Phi comparison Y ≪≫ biprod.mapIso (shiftZero ℤ (derived (H Y))).symm (Iso.refl _)

theorem isZero_iff (j : ℕ) (Y : S) :
    IsZero ((Phi.obj^[j]) (derived Y)) ↔ Subsingleton (selectionIterate Y.val j) := by
  rw [ExternalTensor.Binomial.iteration_isZero_iff Phi derived H 0 3 (shiftedSplit Phi comparison)]
  rw [derived_zero, iterate_val]

/-- Actual Section 2 tests give arbitrarily long finite extinction for this tensor
functor, once its stated stalk comparison is instantiated. -/
theorem extinction (m : ℕ) [NeZero m] :
    (∀ j < m, ¬ IsZero ((Phi.obj^[j]) (derived (test m)))) ∧
      IsZero ((Phi.obj^[m]) (derived (test m))) := by
  constructor
  · intro j hj hz
    have hs := (isZero_iff Phi comparison j (test m)).mp hz
    have hn := selectionIterate_test_nontrivial m j hj
    exact @not_subsingleton _ hn hs
  · exact (isZero_iff Phi comparison m (test m)).mpr (selectionIterate_test_subsingleton m)
end LittleFinitistic.SelectedIteration

end

end OAI
