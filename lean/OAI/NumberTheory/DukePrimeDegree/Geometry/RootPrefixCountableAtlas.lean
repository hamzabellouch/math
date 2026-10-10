import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixBoxes
import Mathlib.Topology.Bases

namespace OAI

/-! # Countably many translated root charts cover the quotient -/

noncomputable section
open Set TopologicalSpace

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V]

theorem exists_countable_translates_cover (C : RootPrefixCoordinates n P V)
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n)
    (z₀ : (UpperRootTransverse n × V) × c.Time) :
    ∃ S : Set (G n), S.Countable ∧
      (⋃ g ∈ S, range (C.timeParam c hP hf g)) = univ := by
  have hopen g : IsOpen (range (C.timeParam c hP hf g)) :=
    (C.timeParam_localHomeomorph c hP hf g).isOpenMap.isOpen_range
  obtain ⟨S,_,hS,heq⟩ := isOpen_biUnion_countable (univ : Set (G n))
    (fun g => range (C.timeParam c hP hf g)) (fun g _ => hopen g)
  refine ⟨S,hS,heq.trans ?_⟩
  apply eq_univ_of_forall
  intro x
  induction x using Quotient.inductionOn with
  | _ a =>
    let b := C.groupParam (z₀.1.1,(z₀.1.2,c.remainingWordHomeomorph hP hf z₀.2))
    refine mem_iUnion.mpr ⟨a*b⁻¹,mem_iUnion.mpr ⟨mem_univ _,z₀,?_⟩⟩
    change Quotient.mk _ ((a*b⁻¹)*b) = Quotient.mk _ a
    simp only [inv_mul_cancel_right]

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
