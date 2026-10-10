import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CountableSumVanishing
import Mathlib.Data.Finsupp.ToDFinsupp

namespace OAI

/-! # The constant-family direct sum form of a countable coefficient sum -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule Finsupp.module
variable {G : Type} [Group G]

def finsuppIntegralSumIso (A : Rep.{0} ℤ G) (ι : Type) :
    A.finsupp ι ≅ integralRepresentationSum (fun _ : ι => A) := by
  classical
  refine Rep.mkIso (ρ := A.ρ.finsupp ι)
    (σ := Representation.directSum (fun _ : ι => A.ρ))
    (Representation.Equiv.mk (finsuppLequivDFinsupp ℤ) ?_)
  intro g
  apply Finsupp.lhom_ext'
  intro i
  ext a
  simp [Representation.finsupp_single, Representation.directSum, finsuppLequivDFinsupp]
  rename_i j
  by_cases h : i = j <;> simp [h]

theorem TypeFPInfinity.finsupp_completeCohomology (hG : TypeFPInfinity G)
    (A : Rep.{0} ℤ G) (p : ℕ)
    (hA : Subsingleton (ShiftedCompletedCohomology p A)) :
    Subsingleton (ShiftedCompletedCohomology p (A.finsupp ℕ)) := by
  have hs := hG.countableSum_completeCohomology (fun _ : ℕ => A) p (fun _ => hA)
  let e := (shiftedCompletedCohomologyFunctor p).mapIso (finsuppIntegralSumIso A ℕ)
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p (A.finsupp ℕ))
  intro x
  apply e.toLinearEquiv.injective
  exact hs.elim _ _

end PolycyclicRecognition

end

end OAI
