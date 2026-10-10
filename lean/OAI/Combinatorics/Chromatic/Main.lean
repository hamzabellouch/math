import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WallUnitNegative
import OAI.Combinatorics.Chromatic.Shuffle.RestrictionBGraded
import OAI.Combinatorics.Chromatic.Shuffle.SymbolInternalWeight
import OAI.Combinatorics.Chromatic.Shuffle.GradedShuffle
import OAI.Combinatorics.Chromatic.Walls.RootClosureFacts
import OAI.Combinatorics.Chromatic.Walls.MutationEventualIncoming
import OAI.Combinatorics.Chromatic.Walls.FiniteRefinementImport
import OAI.Combinatorics.Chromatic.Walls.GraphBlockPairing
import OAI.Combinatorics.Chromatic.Witness.ElementaryAlphabetRigidity

namespace OAI

section
namespace ElementaryPositivity.FiniteSearch
variable {n : ℕ} (G : NaturalUnitIntervalGraph n)

theorem exists_successful_table : ∃ t : Table n, Test G t :=
  exists_test G G.historyWitness

def selectedTable : Table n := Encodable.choose (exists_successful_table G)

theorem selectedTable_test : Test G (selectedTable G) :=
  Encodable.choose_spec (exists_successful_table G)

end ElementaryPositivity.FiniteSearch

def elementaryPositivityWitness (n : ℕ)
    (G : ElementaryPositivity.NaturalUnitIntervalGraph n) : G.PermutationWitness where
  theta σ := ElementaryPositivity.FiniteSearch.rowPartition
    (ElementaryPositivity.FiniteSearch.selectedTable G σ.val)
  expansion r := ElementaryPositivity.FiniteSearch.uniform_expansion_of_test
    G G.historyWitness _ (ElementaryPositivity.FiniteSearch.selectedTable_test G) r

end

end OAI
