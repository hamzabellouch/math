import OAI.Combinatorics.ContingencyTables.Counting.CompanionArithmeticProposal
import OAI.Combinatorics.ContingencyTables.Sampling.SmallPatternProgram

namespace OAI

/-! # Polynomial validation of paired binary states

The bounded-profile arithmetic test specializes to width one.
Thus the companion's state filter is a concrete list program on the two
coordinates of every labelled pair.
-/

namespace ContingencyTables.CompanionChainValidator
open CommonBasesFPRAS TwoLiftStates ProfilePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

noncomputable section

variable {P : Type*} [Fintype P]

omit [Fintype P] in
lemma single_iff_occupancy (S : Set (P×Bool)) (p : P) :
    PairSingle (pair p) S ↔ occupancy S p=1 := by
  unfold PairSingle TwoLiftStates.pair occupancy
  by_cases h0 : (p,false)∈S <;> by_cases h1 : (p,true)∈S <;> simp [h0,h1]

omit [Fintype P] in
lemma empty_iff_occupancy (S : Set (P×Bool)) (p : P) :
    PairEmpty (pair p) S ↔ occupancy S p=0 := by
  unfold PairEmpty TwoLiftStates.pair occupancy
  by_cases h0 : (p,false)∈S <;> by_cases h1 : (p,true)∈S <;> simp [h0,h1]

omit [Fintype P] in
lemma full_iff_occupancy (S : Set (P×Bool)) (p : P) :
    PairFull (pair p) S ↔ occupancy S p=2 := by
  unfold PairFull TwoLiftStates.pair occupancy
  by_cases h0 : (p,false)∈S <;> by_cases h1 : (p,true)∈S <;> simp [h0,h1]

lemma plain_iff_occupancy (S : Set (P×Bool)) :
    PlainState pairs S ↔ ∀ p,occupancy S p=1 := by
  constructor
  · intro h p
    exact (single_iff_occupancy S p).mp (h (pair p) (pair_mem p))
  · intro h p hp
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
    exact (single_iff_occupancy S q).mpr (h q)

lemma defect_iff_occupancy (S : Set (P×Bool)) (p q : P) :
    DefectState pairs (pair p) (pair q) S ↔ p≠q ∧
      ∀ i,occupancy S i+(if i=p then 1 else 0)=1+(if i=q then 1 else 0) := by
  constructor
  · intro h
    exact ⟨fun he => h.2.2.1 (congrArg pair he),defect_occupancy S p q h⟩
  · rintro ⟨hpq,h⟩
    refine ⟨pair_mem p,pair_mem q,fun he => hpq (pair_injective he),?_,?_,?_⟩
    · apply (empty_iff_occupancy S p).mpr
      have hh := h p
      simp only [ite_true,hpq,ite_false] at hh
      omega
    · apply (full_iff_occupancy S q).mpr
      have hh := h q
      simp only [ite_true,Ne.symm hpq,ite_false,Nat.add_zero] at hh
      omega
    · intro t ht htp htq
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
      apply (single_iff_occupancy S i).mpr
      have hip : i≠p := fun he => htp (congrArg pair he)
      have hiq : i≠q := fun he => htq (congrArg pair he)
      simpa only [hip,hiq,ite_false,Nat.add_zero] using h i

lemma chain_iff_occupancy (S : Set (P×Bool)) :
    ChainState pairs S ↔ (∀ i,occupancy S i=1) ∨
      ∃ p q : P,p≠q ∧ ∀ i,occupancy S i+(if i=p then 1 else 0)=1+(if i=q then 1 else 0) := by
  constructor
  · rintro (h|⟨p,q,h⟩)
    · exact Or.inl ((plain_iff_occupancy S).mp h)
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp h.1
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp h.2.1
      exact Or.inr ⟨a,b,(defect_iff_occupancy S a b).mp h⟩
  · rintro (h|⟨p,q,h⟩)
    · exact Or.inl ((plain_iff_occupancy S).mpr h)
    · exact Or.inr ⟨pair p,pair q,(defect_iff_occupancy S p q).mpr h⟩

/-- Width one is exactly the companion's labelled paired-state test. -/
theorem paired_pattern_iff {m : ℕ} (e : Fin m ≃ P) (S : Set (P×Bool)) :
    patternTest ((List.ofFn (fun i => if (e i,false)∈S then 1 else 0),
      List.ofFn (fun i => if (e i,true)∈S then 1 else 0)),1)=true ↔ ChainState pairs S := by
  rw [patternTest_ofFn,chain_iff_occupancy]
  change (∀ i,occupancy S (e i)=1) ∨
    (∃ p q : Fin m,p≠q ∧ ∀ i,occupancy S (e i)+(if i=p then 1 else 0)=
      1+(if i=q then 1 else 0)) ↔ _
  constructor
  · rintro (h|⟨p,q,hpq,h⟩)
    · exact Or.inl (fun i => by simpa using h (e.symm i))
    · refine Or.inr ⟨e p,e q,fun he => hpq (e.injective he),?_⟩
      intro i
      simpa only [Equiv.apply_symm_apply,e.symm_apply_eq] using h (e.symm i)
  · rintro (h|⟨p,q,hpq,h⟩)
    · exact Or.inl (fun i => h (e i))
    · refine Or.inr ⟨e.symm p,e.symm q,fun he => hpq (e.symm.injective he),?_⟩
      intro i
      simpa only [←e.eq_symm_apply] using h (e i)

end

abbrev ValidatorInput := List (ℕ×ℕ)×List ℕ

def pairFirstLookup : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.1.getD z.2.1 0) :=
  composition (pair first (composition second first)) (getDFast 0)

def pairSecondLookup : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.1.getD z.2.2 0) :=
  composition (pair first (composition second second)) (getDFast 0)

lemma polynomial_pairFirstLookup : PolynomialTime pairFirstLookup :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast 0)

lemma polynomial_pairSecondLookup : PolynomialTime pairSecondLookup :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0)

def pairedStateTest (z : ValidatorInput) : Bool :=
  patternTest (((z.1.map (fun ij => z.2.getD ij.1 0)),
    (z.1.map (fun ij => z.2.getD ij.2 0))),1)

def pairedStateTestRealizer : Realizer pairedStateTest :=
  composition (pair (pair
    (composition (pair second first) (mapWith pairFirstLookup))
    (composition (pair second first) (mapWith pairSecondLookup))) (constant 1)) patternTestRealizer

theorem polynomial_pairedStateTest : PolynomialTime pairedStateTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_mapWith polynomial_pairFirstLookup))
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_mapWith polynomial_pairSecondLookup))) (polynomial_constant 1)) polynomial_patternTest

noncomputable section
open CompanionFactorialApplication CompanionArithmeticProposal
variable {I J : Type} [Fintype I] [Fintype J]

def labelEquiv (A : Instance I J) : Fin (Fintype.card (Labels A)) ≃ Labels A :=
  (Fintype.equivFin _).symm

def pairCatalog (A : Instance I J) : List (ℕ×ℕ) :=
  List.ofFn (fun i => ((coordinateEquiv A (labelEquiv A i,false)).val,
    (coordinateEquiv A (labelEquiv A i,true)).val))

/-- This list program checks the literal companion state, with no
feasibility oracle or whole-state enumeration. -/
theorem pairedStateTest_encode (A : Instance I J) (S : Set (Labels A×Bool)) :
    pairedStateTest (pairCatalog A,encodeSet (coordinateEquiv A) S)=true ↔ ChainState pairs S := by
  unfold pairedStateTest pairCatalog
  simp only [List.map_ofFn]
  change patternTest ((List.ofFn (fun i : Fin (Fintype.card (Labels A)) =>
      (encodeSet (coordinateEquiv A) S).getD
        (coordinateEquiv A (labelEquiv A i,false)).val 0),
    List.ofFn (fun i : Fin (Fintype.card (Labels A)) =>
      (encodeSet (coordinateEquiv A) S).getD
        (coordinateEquiv A (labelEquiv A i,true)).val 0)),1)=true ↔ _
  simp only [encodeSet,getD_setProfile,setProfile,coordinateSet,Set.mem_preimage,
    Equiv.symm_apply_apply]
  exact paired_pattern_iff (labelEquiv A) S

end
end ContingencyTables.CompanionChainValidator

end OAI
