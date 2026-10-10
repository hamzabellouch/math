import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompleteVanishingExactFunctor
import Mathlib.Logic.Encodable.Basic

namespace OAI

/-! # Countably generated free representations are retracts of one fixed free module -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {Q G : Type} [Group Q] [Group G]

def countableFreeRetract (α : Type) [Countable α] :
    Retract (Rep.free ℤ Q α) (Rep.free ℤ Q ℕ) := by
  classical
  let := Encodable.ofCountable α
  let i : Rep.free ℤ Q α ⟶ Rep.free ℤ Q ℕ :=
    Rep.freeLift ℤ Q _ (fun a => Finsupp.single (Encodable.encode a) (MonoidAlgebra.single 1 1))
  let r : Rep.free ℤ Q ℕ ⟶ Rep.free ℤ Q α :=
    Rep.freeLift ℤ Q _ (fun n => match Encodable.decode (α := α) n with
      | some a => Finsupp.single a (MonoidAlgebra.single 1 1)
      | none => 0)
  refine ⟨i, r, ?_⟩
  apply Rep.free_ext
  intro a
  change r.hom (i.hom (Finsupp.single a (MonoidAlgebra.single 1 1))) =
    Finsupp.single a (MonoidAlgebra.single 1 1)
  simp [i, r, Rep.freeLift, Representation.freeLift_single_single]

variable (F : Rep.{0} ℤ Q ⥤ Rep.{0} ℤ G) [F.Additive]
variable [F.PreservesHomology] [F.PreservesMonomorphisms] [F.PreservesEpimorphisms]

theorem exactFunctor_complete_vanishing_of_countable_free [Countable Q]
    (hfree : ∀ p : ℕ,
      Subsingleton (ShiftedCompletedCohomology p (F.obj (Rep.free ℤ Q ℕ))))
    (A : Rep.{0} ℤ Q) [Countable A] (d : ℕ)
    (hd : HasProjectiveDimensionLE A d) (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p (F.obj A)) := by
  apply exactFunctor_complete_vanishing_of_finite_dimension F _ A d hd p
  intro B _ p
  exact shiftedCompleteCohomology_subsingleton_of_retract p
    ((countableFreeRetract (Q := Q) {b : B // b ≠ 0}).map F) (hfree p)

end PolycyclicRecognition

end

end OAI
