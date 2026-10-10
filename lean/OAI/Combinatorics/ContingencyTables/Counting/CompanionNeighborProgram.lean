import OAI.Combinatorics.ContingencyTables.Counting.CompanionChainValidator

namespace OAI

/-! # Executable valid-neighbor lists and their binary draw

This composes the actual integer-exchange program with the paired-state
validator and the bounded list-index program. The output code is exactly
the encoding of the semantic proposal, including its failure outcome.
-/

namespace ContingencyTables.CompanionNeighborProgram
open CompanionChainValidator CompanionArithmeticProposal CompanionFactorialApplication
open CompanionBooleanPhase ProfilePrograms MatchingFPRAS.TreeTyped
open CommonBasesFPRAS
open scoped BigOperators Classical

def validExchanges (z : ValidatorInput) : List (List ℕ) :=
  (binaryExchanges z.2).filter (fun xs => pairedStateTest (z.1,xs))

def validExchangesRealizer : Realizer validExchanges :=
  composition (pair first (composition second binaryExchangesRealizer))
    (filterWith pairedStateTestRealizer)

theorem polynomial_validExchanges : PolynomialTime validExchangesRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_binaryExchanges))
    (polynomial_filterWith polynomial_pairedStateTest)

def codeProposal (z : ValidatorInput×List Bool) : Option (List ℕ) :=
  listWordChoice (validExchanges z.1,z.2)

def codeProposalRealizer : Realizer codeProposal :=
  composition (pair (composition first validExchangesRealizer) second) listWordChoiceRealizer

/-- All loops traverse the supplied profile, pair catalog or quadratic
coordinate list. A large binary draw index never determines a loop. -/
theorem polynomial_codeProposal : PolynomialTime codeProposalRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_validExchanges) polynomial_second)
    polynomial_listWordChoice

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma validExchanges_encode (A : Instance I J) (S : State A) :
    validExchanges (pairCatalog A,encodeSet (coordinateEquiv A) S.val)=
      (neighbors A S).map (fun T => encodeSet (coordinateEquiv A) T.val) := by
  unfold validExchanges neighbors neighborStates neighborSets
  rw [List.map_filterMap,List.filterMap_map,←List.filterMap_eq_filter]
  apply List.filterMap_congr
  intro xs hxs
  obtain ⟨T,hT,rfl⟩ := (mem_raw_codes (coordinateEquiv A) S.val xs).mp hxs
  simp only [Function.comp_apply,decode_encode]
  by_cases h : ChainState TwoLiftStates.pairs T
  · have hp : pairedStateTest (pairCatalog A,encodeSet (coordinateEquiv A) T)=true :=
      (pairedStateTest_encode A T).mpr h
    simp only [dite_eq_left h,Option.map_some,Option.guard,hp,ite_true]
  · have hp : pairedStateTest (pairCatalog A,encodeSet (coordinateEquiv A) T)=false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact h ((pairedStateTest_encode A T).mp ht)
    simp only [dite_eq_right h,Option.map_none,Option.guard,hp,Bool.false_eq_true,ite_false]

/-- The public binary program computes the exact semantic draw. -/
theorem codeProposal_eq (A : Instance I J) (S : State A)
    (bits : Fin (proposalBits A) → Bool) :
    codeProposal ((pairCatalog A,encodeSet (coordinateEquiv A) S.val),List.ofFn bits)=
      (CompanionArithmeticProposal.proposal A S bits).map
        (fun T => encodeSet (coordinateEquiv A) T.val) := by
  rw [codeProposal,validExchanges_encode]
  simp only [listWordChoice,CompanionArithmeticProposal.proposal,List.getElem?_map]

end
end ContingencyTables.CompanionNeighborProgram

end OAI
