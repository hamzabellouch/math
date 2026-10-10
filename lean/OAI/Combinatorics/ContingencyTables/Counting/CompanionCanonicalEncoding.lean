import OAI.Combinatorics.ContingencyTables.Machines.CanonicalInitialEncoding
import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitialDraw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOrderedProposal

namespace OAI

/-! # A common explicit encoding for initialization and proposals

Cells follow `cellEnum`, their copies follow increasing finite indices,
and each copy contributes its false and true coordinates consecutively.
The polynomial initializer computes exactly this encoding of the actual
initial draw. The same order may therefore be used by the proposal scan.
-/

namespace ContingencyTables.CompanionCanonicalEncoding

open CommonBasesFPRAS TwoLiftStates CompanionFactorialApplication
open InitialTransversals InitialFactorialBits CompanionInitialDraw
open CompanionArithmeticProposal CompanionOrderedProposal
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def copyEquiv (A : Instance I J) : Labels A ≃ Copy (cellCapacity A) :=
  Equiv.sigmaCongrLeft' (cellEnum A)

def pairEquiv (A : Instance I J) : (Labels A×Bool) ≃ (Copy (cellCapacity A)×Bool) :=
  Equiv.prodCongr (copyEquiv A) (Equiv.refl Bool)

def coordinateOrder (A : Instance I J) : (Labels A×Bool) ≃
    Fin (CanonicalInitialEncoding.pairOrder (cellCapacity A)).length :=
  (pairEquiv A).trans (CanonicalInitialEncoding.coordinateEquiv (cellCapacity A))

lemma encodeSet_reindex (A : Instance I J) (S : Set (Labels A×Bool)) :
    encodeSet (coordinateOrder A) S=
      encodeSet (CanonicalInitialEncoding.coordinateEquiv (cellCapacity A))
        ((pairEquiv A).symm ⁻¹' S) := rfl

/-- Reindexing the physical initial draw gives the independent cell
choices used by the actual list initializer. -/
lemma initial_preimage (A : Instance I J) (B : ℕ)
    (bits : Fin (initialBits A B) → Bool) :
    (pairEquiv A).symm ⁻¹' (draw A B bits).val.val=
      encode (cellCapacity A) (drawChoices (cellCapacity A) B bits) := by
  ext p
  rcases p with ⟨⟨i,k⟩,side⟩
  have hc := Equiv.piCongrLeft'_symm_apply_apply
    (fun s : SmallCell A => Finset (Fin (A.b s.val.1 s.val.2)))
    (cellEnum A) (drawChoices (cellCapacity A) B bits) i
  cases side
  · change k∈(choiceEquiv (fun s : SmallCell A => A.b s.val.1 s.val.2)
      (cellEnum A) (drawChoices (cellCapacity A) B bits)) ((cellEnum A).symm i) ↔
        k∈drawChoices (cellCapacity A) B bits i
    exact Iff.of_eq (congrArg (fun S => k∈S) hc)
  · change k∉(choiceEquiv (fun s : SmallCell A => A.b s.val.1 s.val.2)
      (cellEnum A) (drawChoices (cellCapacity A) B bits)) ((cellEnum A).symm i) ↔
        k∉drawChoices (cellCapacity A) B bits i
    exact Iff.of_eq (congrArg (fun S => k∉S) hc)

/-- The polynomial binary initializer emits precisely the code of the
literal `PlainIndex` output with its distributional error bound. -/
theorem initialCode_eq (A : Instance I J) (B : ℕ) (hB : 0<B)
    (bits : Fin (initialBits A B) → Bool) :
    CanonicalInitialEncoding.initialCode ((List.ofFn (cellCapacity A),B),List.ofFn bits)=
      encodeSet (coordinateOrder A) (draw A B bits).val.val := by
  rw [encodeSet_reindex,initial_preimage]
  exact CanonicalInitialEncoding.initialCode_ofFn (cellCapacity A) B hB bits

/-- The canonical initializer encoding can be fed directly to an
arithmetic proposal with the same dyadic transition law. -/
theorem canonicalProposal_law (A : Instance I J) (S : CompanionBooleanPhase.State A) :
    FirstSuccess.mapLaw
      (FirstSuccess.uniformLaw (α := Fin (CompanionBooleanPhase.proposalBits A) → Bool))
      (orderedProposal A (coordinateOrder A) S)=
    FirstSuccess.mapLaw
      (FirstSuccess.uniformLaw (α := Fin (CompanionBooleanPhase.proposalBits A) → Bool))
      (CompanionBooleanPhase.proposal A S) :=
  orderedProposal_law A (coordinateOrder A) S

end
end ContingencyTables.CompanionCanonicalEncoding

end OAI
