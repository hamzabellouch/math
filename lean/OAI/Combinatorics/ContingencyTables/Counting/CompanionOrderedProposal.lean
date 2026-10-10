import OAI.Combinatorics.ContingencyTables.Counting.CompanionNeighborProgram

namespace OAI

/-! # The companion proposal with a specified coordinate order

The coordinate scan and its paired-state validator work with the same
explicit order used by the initializer. Its dyadic proposal law is
independent of this order, including unused proposal words.
-/

namespace ContingencyTables.CompanionOrderedProposal

open CommonBasesFPRAS TwoLiftStates CompanionFactorialApplication
open CompanionArithmeticProposal CompanionChainValidator CompanionNeighborProgram
open CompanionBooleanPhase FirstSuccess ResidualMixture ProfilePrograms
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {m p : ℕ}

def orderedNeighbors (e : (Labels A×Bool) ≃ Fin m) (S : State A) : List (State A) :=
  neighborStates e pairs S

lemma mem_orderedNeighbors (e : (Labels A×Bool) ≃ Fin m) (S T : State A) :
    T∈orderedNeighbors A e S ↔ ExchangeAdjacent S.val T.val :=
  mem_neighborStates e pairs S T

lemma orderedNeighbors_nodup (e : (Labels A×Bool) ≃ Fin m) (S : State A) :
    (orderedNeighbors A e S).Nodup := neighborStates_nodup e pairs S

lemma orderedNeighbors_length (e : (Labels A×Bool) ≃ Fin m) (S : State A) :
    (orderedNeighbors A e S).length≤2^proposalBits A := by
  have he : (orderedNeighbors A e S).toFinset=
      Finset.univ.filter (fun T : State A => ExchangeAdjacent S.val T.val) := by
    ext T
    simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and,
      mem_orderedNeighbors]
  rw [←List.toFinset_card_of_nodup (orderedNeighbors_nodup A e S),he]
  simpa only [Fintype.card_subtype] using proposal_codes A S

def orderedProposal (e : (Labels A×Bool) ≃ Fin m) (S : State A)
    (bits : Fin (proposalBits A) → Bool) : Option (State A) :=
  listWordChoice (orderedNeighbors A e S,List.ofFn bits)

lemma orderedProposal_mass (e : (Labels A×Bool) ≃ Fin m) (S T : State A) :
    (mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
      (orderedProposal A e S)).mass (some T)=
      if ExchangeAdjacent S.val T.val then 1/(2:ℚ)^proposalBits A else 0 := by
  exact (listWordChoice_mass (orderedNeighbors A e S) (orderedNeighbors_nodup A e S)
    (proposalBits A) (orderedNeighbors_length A e S) T).trans
      (by simp only [mem_orderedNeighbors])

/-- Every complete coordinate order has the analysed proposal law. -/
theorem orderedProposal_law (e : (Labels A×Bool) ≃ Fin m) (S : State A) :
    mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (orderedProposal A e S)=
      mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
        (CompanionBooleanPhase.proposal A S) := by
  let u := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (orderedProposal A e S)
  let v := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
    (CompanionBooleanPhase.proposal A S)
  have hs (T : State A) : u.mass (some T)=v.mass (some T) :=
    (orderedProposal_mass A e S T).trans (CompanionBooleanPhase.proposal_mass A S T).symm
  change u=v
  apply RationalLaw.ext
  funext T
  cases T with
  | some T => exact hs T
  | none =>
    have hu := u.total
    have hv := v.total
    simp only [Fintype.sum_option] at hu hv
    simp_rw [hs] at hu
    linarith

def orderedCatalog (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin m) : List (ℕ×ℕ) :=
  List.ofFn (fun i => ((e (g i,false)).val,(e (g i,true)).val))

lemma pairedStateTest_ordered (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin m)
    (S : Set (Labels A×Bool)) :
    pairedStateTest (orderedCatalog A g e,encodeSet e S)=true ↔ ChainState pairs S := by
  unfold pairedStateTest orderedCatalog
  simp only [List.map_ofFn]
  change patternTest ((List.ofFn (fun i : Fin p =>
      (encodeSet e S).getD (e (g i,false)).val 0),
    List.ofFn (fun i : Fin p => (encodeSet e S).getD (e (g i,true)).val 0)),1)=true ↔ _
  simp only [encodeSet,getD_setProfile,setProfile,coordinateSet,Set.mem_preimage,
    Equiv.symm_apply_apply]
  exact paired_pattern_iff g S

lemma validExchanges_ordered (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin m)
    (S : State A) :
    validExchanges (orderedCatalog A g e,encodeSet e S.val)=
      (orderedNeighbors A e S).map (fun T => encodeSet e T.val) := by
  unfold validExchanges orderedNeighbors neighborStates neighborSets
  rw [List.map_filterMap,List.filterMap_map,←List.filterMap_eq_filter]
  apply List.filterMap_congr
  intro xs hxs
  obtain ⟨T,hT,rfl⟩ := (mem_raw_codes e S.val xs).mp hxs
  simp only [Function.comp_apply,decode_encode]
  by_cases h : ChainState pairs T
  · have hp : pairedStateTest (orderedCatalog A g e,encodeSet e T)=true :=
      (pairedStateTest_ordered A g e T).mpr h
    simp only [dite_eq_left h,Option.map_some,Option.guard,hp,ite_true]
  · have hp : pairedStateTest (orderedCatalog A g e,encodeSet e T)=false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact h ((pairedStateTest_ordered A g e T).mp ht)
    simp only [dite_eq_right h,Option.map_none,Option.guard,hp,Bool.false_eq_true,ite_false]

/-- The polynomial list program returns exactly the encoded state drawn
by the ordered proposal; no enumeration of all chain states is needed. -/
theorem codeProposal_ordered (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin m)
    (S : State A) (bits : Fin (proposalBits A) → Bool) :
    codeProposal ((orderedCatalog A g e,encodeSet e S.val),List.ofFn bits)=
      (orderedProposal A e S bits).map (fun T => encodeSet e T.val) := by
  rw [codeProposal,validExchanges_ordered]
  simp only [listWordChoice,orderedProposal,List.getElem?_map]

end
end ContingencyTables.CompanionOrderedProposal

end OAI
