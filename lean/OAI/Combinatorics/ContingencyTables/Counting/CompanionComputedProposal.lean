import OAI.Combinatorics.ContingencyTables.Counting.CompanionComputedInitial
import OAI.Combinatorics.ContingencyTables.Machines.PairedCatalogProgram

namespace OAI

/-! # The companion proposal with computed metadata

The executable proposal receives only a binary profile and fresh bits.
It computes the consecutive-pair catalog itself and scans coordinate
exchanges. Its semantic law is the same ordered proposal law.
-/

namespace ContingencyTables.CompanionComputedProposal

open MatchingFPRAS.TreeTyped CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOrderedProposal CompanionNeighborProgram
open CompanionBooleanPhase
open scoped Classical

def proposalProgram (z : List ℕ×List Bool) : Option (List ℕ) :=
  codeProposal ((PairedCatalogProgram.catalog z.1,z.1),z.2)

def catalogInputRealizer : Realizer (fun z : List ℕ×List Bool => PairedCatalogProgram.catalog z.1) :=
  composition (f := fun z : List ℕ×List Bool => z.1) (g := PairedCatalogProgram.catalog)
    first PairedCatalogProgram.catalogRealizer

def proposalProgramRealizer : Realizer proposalProgram :=
  composition (f := fun z : List ℕ×List Bool => ((PairedCatalogProgram.catalog z.1,z.1),z.2))
    (g := codeProposal) (pair (pair catalogInputRealizer first) second) codeProposalRealizer

theorem polynomial_proposalProgram : PolynomialTime proposalProgramRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first PairedCatalogProgram.polynomial_catalog)
    polynomial_first) polynomial_second) polynomial_codeProposal

noncomputable section
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

def pairLabels : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length ≃ Labels A :=
  (PairedCatalogProgram.labelOrder (capacities A)).trans (copyOrder A).symm

lemma pair_coordinate (i : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length)
    (side : Bool) :
    coordinateOrder A (pairLabels A i,side)=
      CanonicalInitialEncoding.coordinateEquiv (capacities A)
        (PairedCatalogProgram.labelOrder (capacities A) i,side) := by
  simp [coordinateOrder,pairOrder,pairLabels]

lemma generated_catalog (S : Set (Labels A×Bool)) :
    PairedCatalogProgram.catalog (encodeSet (coordinateOrder A) S)=
      orderedCatalog A (pairLabels A) (coordinateOrder A) := by
  have he : encodeSet (coordinateOrder A) S=
      encodeSet (CanonicalInitialEncoding.coordinateEquiv (capacities A))
        ((pairOrder A).symm ⁻¹' S) := rfl
  rw [he,PairedCatalogProgram.catalog_encode]
  unfold orderedCatalog
  apply congrArg List.ofFn
  funext i
  rw [pair_coordinate,pair_coordinate]

/-- Every proposed code is the encoding of the actual ordered proposal
state, and unused binary indices give precisely the same `none` result. -/
theorem proposalProgram_eq (S : State A) (bits : Fin (proposalBits A) → Bool) :
    proposalProgram (encodeSet (coordinateOrder A) S.val,List.ofFn bits)=
      (orderedProposal A (coordinateOrder A) S bits).map
        (fun T => encodeSet (coordinateOrder A) T.val) := by
  unfold proposalProgram
  rw [generated_catalog]
  exact codeProposal_ordered A (pairLabels A) (coordinateOrder A) S bits

end
end ContingencyTables.CompanionComputedProposal

end OAI
