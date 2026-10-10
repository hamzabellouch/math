import OAI.Combinatorics.ContingencyTables.Machines.BinaryExchangeProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionBooleanPhase
import OAI.Combinatorics.ContingencyTables.Machines.ListWordProgram
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordDependent

namespace OAI

/-! # An explicit coordinate-list proposal for the companion chain

Only ordered coordinates are enumerated. The arithmetic binary-profile
program generates the possible exchanges, after which the actual chain
state predicate removes disallowed states. A dyadic list index has exactly
the same proposal law as the abstract injection.
-/

namespace ContingencyTables.CompanionArithmeticProposal
open CommonBasesFPRAS ProfilePrograms FirstSuccess ResidualMixture FairBits
open CompanionFactorialApplication CompanionBooleanPhase TwoLiftStates
open scoped BigOperators Classical

noncomputable section

section Coordinates
variable {Γ : Type*} [Fintype Γ] {n : ℕ} (e : Γ ≃ Fin n)

def coordinateSet (S : Set Γ) : Set (Fin n) := e.symm ⁻¹' S

def physicalSet (S : Set (Fin n)) : Set Γ := e ⁻¹' S

omit [Fintype Γ] in
@[simp] lemma physical_coordinate (S : Set Γ) : physicalSet e (coordinateSet e S)=S := by
  ext a
  simp [physicalSet,coordinateSet]

omit [Fintype Γ] in
@[simp] lemma coordinate_physical (S : Set (Fin n)) : coordinateSet e (physicalSet e S)=S := by
  ext a
  simp [physicalSet,coordinateSet]

omit [Fintype Γ] in
lemma adjacent_preimage {Δ : Type*} [Fintype Δ] (f : Γ ≃ Δ) (S T : Set Δ)
    (h : ExchangeAdjacent S T) : ExchangeAdjacent (f ⁻¹' S) (f ⁻¹' T) := by
  obtain ⟨B,a,b,hab,ha,hb,rfl,rfl⟩ := h
  refine ⟨f ⁻¹' B,f.symm a,f.symm b,fun he => hab (f.symm.injective he),?_,?_,?_,?_⟩
  · simpa using ha
  · simpa using hb
  · ext x
    simp only [Set.mem_preimage,Set.mem_insert_iff]
    rw [←f.eq_symm_apply]
  · ext x
    simp only [Set.mem_preimage,Set.mem_insert_iff]
    rw [←f.eq_symm_apply]

lemma adjacent_coordinate_iff (S T : Set Γ) :
    ExchangeAdjacent (coordinateSet e S) (coordinateSet e T) ↔ ExchangeAdjacent S T := by
  constructor
  · intro h
    have hh : ExchangeAdjacent (physicalSet e (coordinateSet e S))
        (physicalSet e (coordinateSet e T)) := adjacent_preimage e _ _ h
    simpa only [physical_coordinate] using hh
  · exact adjacent_preimage e.symm S T

def encodeSet (S : Set Γ) : List ℕ := List.ofFn (setProfile (coordinateSet e S))

def decodeSet (xs : List ℕ) : Set Γ := {a | xs.getD (e a).val 0=1}

omit [Fintype Γ] in
@[simp] lemma decode_encode (S : Set Γ) : decodeSet e (encodeSet e S)=S := by
  ext a
  simp only [decodeSet,Set.mem_ofPred_eq,encodeSet,getD_setProfile,setProfile,
    coordinateSet,Set.mem_preimage,Equiv.symm_apply_apply]
  by_cases ha : a∈S <;> simp [ha]

omit [Fintype Γ] in
lemma encode_injective : Function.Injective (encodeSet e) := by
  intro S T he
  have hd := congrArg (decodeSet e) he
  simpa only [decode_encode] using hd

omit [Fintype Γ] in
lemma encode_physical (U : Set (Fin n)) :
    encodeSet e (physicalSet e U)=List.ofFn (setProfile U) := by
  simp only [encodeSet,coordinate_physical]

omit [Fintype Γ] in
lemma decode_profile (U : Set (Fin n)) :
    decodeSet e (List.ofFn (setProfile U))=physicalSet e U := by
  rw [←encode_physical e U,decode_encode]

/-- The executable integer update enumerates exactly the set exchanges. -/
theorem mem_raw_codes (S : Set Γ) (xs : List ℕ) :
    xs∈binaryExchanges (encodeSet e S) ↔
      ∃ T : Set Γ,ExchangeAdjacent S T ∧ xs=encodeSet e T := by
  rw [encodeSet,mem_binaryExchanges_setProfile]
  constructor
  · rintro ⟨i,j,hi,hj,rfl⟩
    let U := insert i (coordinateSet e S\{j})
    have hU : ExchangeAdjacent (coordinateSet e S) U :=
      exchangedSet_adjacent _ (⟨j,hj⟩,⟨i,hi⟩)
    refine ⟨physicalSet e U,?_,(encode_physical e U).symm⟩
    apply (adjacent_coordinate_iff e S _).mp
    simpa only [coordinate_physical] using hU
  · rintro ⟨T,hST,rfl⟩
    obtain ⟨j,hj,i,hi,he⟩ := ((adjacent_coordinate_iff e S T).mpr hST).move
    exact ⟨i,j,hi,hj,by rw [encodeSet,he]⟩

def neighborSets (S : Set Γ) : List (Set Γ) :=
  (binaryExchanges (encodeSet e S)).map (decodeSet e)

lemma mem_neighborSets (S T : Set Γ) : T∈neighborSets e S ↔ ExchangeAdjacent S T := by
  simp only [neighborSets,List.mem_map,mem_raw_codes]
  constructor
  · rintro ⟨xs,⟨U,hU,rfl⟩,he⟩
    have he' : U=T := by simpa only [decode_encode] using he
    exact he' ▸ hU
  · intro h
    exact ⟨encodeSet e T,⟨T,h,rfl⟩,decode_encode e T⟩

lemma neighborSets_nodup (S : Set Γ) : (neighborSets e S).Nodup := by
  apply (binaryExchanges_nodup (coordinateSet e S)).map_on
  intro xs hxs ys hys he
  obtain ⟨T,hT,rfl⟩ := (mem_raw_codes e S xs).mp hxs
  obtain ⟨U,hU,rfl⟩ := (mem_raw_codes e S ys).mp hys
  simpa only [decode_encode] using congrArg (encodeSet e) he

/-- The state filter is applied after the quadratic coordinate scan. -/
def neighborStates (gs : List (Γ×Γ)) (S : ChainIndex gs) : List (ChainIndex gs) :=
  (neighborSets e S.val).filterMap (fun T => if h : ChainState gs T then some ⟨T,h⟩ else none)

omit [Fintype Γ] in
lemma stateFilter_eq_some (gs : List (Γ×Γ)) (T : Set Γ) (U : ChainIndex gs) :
    (if h : ChainState gs T then some (⟨T,h⟩ : ChainIndex gs) else none)=some U ↔ T=U.val := by
  by_cases h : ChainState gs T
  · simp only [dite_eq_left h,Option.some.injEq]
    exact Subtype.ext_iff
  · simp only [dite_eq_right h,reduceCtorEq,false_iff]
    intro he
    exact h (he.symm ▸ U.property)

lemma mem_neighborStates (gs : List (Γ×Γ)) (S T : ChainIndex gs) :
    T∈neighborStates e gs S ↔ ExchangeAdjacent S.val T.val := by
  simp only [neighborStates,List.mem_filterMap,stateFilter_eq_some]
  constructor
  · rintro ⟨U,hU,rfl⟩
    exact (mem_neighborSets e S.val T.val).mp hU
  · intro h
    exact ⟨T.val,(mem_neighborSets e S.val T.val).mpr h,rfl⟩

lemma neighborStates_nodup (gs : List (Γ×Γ)) (S : ChainIndex gs) :
    (neighborStates e gs S).Nodup := by
  apply List.Nodup.filterMap _ (neighborSets_nodup e S.val)
  intro T U V hT hU
  have hTV := (stateFilter_eq_some gs T V).mp (Option.mem_def.mp hT)
  have hUV := (stateFilter_eq_some gs U V).mp (Option.mem_def.mp hU)
  exact hTV.trans hUV.symm

end Coordinates

variable {I J : Type} [Fintype I] [Fintype J]

def coordinateEquiv (A : Instance I J) : (Labels A×Bool) ≃ Fin (Fintype.card (Labels A×Bool)) :=
  Fintype.equivFin _

def neighbors (A : Instance I J) (S : State A) : List (State A) :=
  neighborStates (coordinateEquiv A) pairs S

@[simp] theorem mem_neighbors (A : Instance I J) (S T : State A) :
    T∈neighbors A S ↔ ExchangeAdjacent S.val T.val :=
  mem_neighborStates _ _ _ _

theorem neighbors_nodup (A : Instance I J) (S : State A) : (neighbors A S).Nodup :=
  neighborStates_nodup _ _ _

theorem neighbors_length (A : Instance I J) (S : State A) :
    (neighbors A S).length≤2^proposalBits A := by
  have he : (neighbors A S).toFinset=Finset.univ.filter (fun T : State A => ExchangeAdjacent S.val T.val) := by
    ext T
    simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and,mem_neighbors]
  rw [←List.toFinset_card_of_nodup (neighbors_nodup A S),he]
  simpa only [Fintype.card_subtype] using proposal_codes A S

/-- The selection stage is the actual binary list-index program. -/
def proposal (A : Instance I J) (S : State A) (bits : Fin (proposalBits A) → Bool) : Option (State A) :=
  listWordChoice (neighbors A S,List.ofFn bits)

theorem proposal_mass (A : Instance I J) (S T : State A) :
    (mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)).mass (some T)=
      if ExchangeAdjacent S.val T.val then 1/(2:ℚ)^proposalBits A else 0 := by
  exact (listWordChoice_mass (neighbors A S) (neighbors_nodup A S)
    (proposalBits A) (neighbors_length A S) T).trans (by simp only [mem_neighbors])

/-- The explicit arithmetic enumeration changes no proposal probabilities,
including the unused-code outcome. -/
theorem proposal_law (A : Instance I J) (S : State A) :
    mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)=
      mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
        (CompanionBooleanPhase.proposal A S) := by
  let p := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)
  let q := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
    (CompanionBooleanPhase.proposal A S)
  have hs (T : State A) : p.mass (some T)=q.mass (some T) :=
    (proposal_mass A S T).trans (CompanionBooleanPhase.proposal_mass A S T).symm
  change p=q
  apply RationalLaw.ext
  funext T
  cases T with
  | some T => exact hs T
  | none =>
    have hp := p.total
    have hq := q.total
    simp only [Fintype.sum_option] at hp hq
    simp_rw [hs] at hp
    linarith

end
end ContingencyTables.CompanionArithmeticProposal

end OAI
