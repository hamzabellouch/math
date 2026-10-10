import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulk

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.CanonicalHistoryLeafBulk
open Construction Conclusion HistoryResidueRegular

variable {q : ℕ} [Fact q.Prime]

theorem bulkSamples_ne_zero (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (hr : Regular q (decodeHistory sources (Template.initial m k) V l a c))
    (u : Fin (2^l) × Fin m) :
    (bulkSamples sources m k l x u.1 u.2 : ZMod q)≠0 := by
  apply value_ne_zero hr
  rw [decodeHistory_root]
  simp only [State.values,List.mem_cons]
  right; right
  rw [hx]
  change _ ∈ (List.ofFn (fun i =>
    ({role := (Template.current (Template.initial m k) l)[i].role,
      value := (x i).val,
      origin := (Template.current (Template.initial m k) l)[i].origin} : SmallSlot))).map SmallSlot.value
  rw [List.map_ofFn]
  exact List.mem_ofFn.mpr ⟨((currentBulkPositionEquiv m k l).symm u).val,rfl⟩

def bulkUnits (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (hr : Regular q (decodeHistory sources (Template.initial m k) V l a c))
    (u : Fin (2^l) × Fin m) : (ZMod q)ˣ :=
  Units.mk0 _ (bulkSamples_ne_zero sources m k V l a c x hx hr u)

@[simp] theorem bulkUnits_coe (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (hr : Regular q (decodeHistory sources (Template.initial m k) V l a c))
    (u : Fin (2^l) × Fin m) :
    (bulkUnits sources m k V l a c x hx hr u : ZMod q)=
      (bulkSamples sources m k l x u.1 u.2 : ZMod q) := rfl

theorem decodeHistory_leafBulk (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (hr : Regular q (decodeHistory sources (Template.initial m k) V l a c))
    (path : Tree.Leaves l) :
    HistoryTreeParameters.leafBulk _ hr path=
      ∏ i, bulkUnits sources m k V l a c x hx hr (orderedLeafIndex l path,i) := by
  apply Units.ext
  rw [decodeHistory_leafBulk_coe _ _ _ _ _ _ _ _ hx]
  change _=(Units.coeHom (ZMod q)) (∏ i,
    bulkUnits sources m k V l a c x hx hr (orderedLeafIndex l path,i))
  rw [map_prod]
  rfl

theorem decodeHistory_leafBulk_permuted (b k : ℕ) (bulk : PrimeSource)
    (top : Fin 3→PrimeSource) (comp : Fin k→Fin 2→PrimeSource) (V : ℕ→ℕ)
    (l : ℕ) (a a' : State)
    (c c' : HistoryChoices (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l))
    (hx : a.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l) x)
    (hx' : a'.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)
      (leafBulkAssignmentPermutation b k l bulk top comp σ x))
    (hr : Regular q (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l a c))
    (hr' : Regular q (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l a' c')) (path : Tree.Leaves l) :
    HistoryTreeParameters.leafBulk _ hr' path=
      ∏ i, bulkUnits (initialSourceFamily b k bulk top comp) (2*b) k V l a c x hx hr
        (σ (orderedLeafIndex l path,i)) := by
  apply Units.ext
  rw [decodeHistory_leafBulk_coe _ _ _ _ _ _ _ _ hx']
  change _=(Units.coeHom (ZMod q)) (∏ i,
    bulkUnits (initialSourceFamily b k bulk top comp) (2*b) k V l a c x hx hr
      (σ (orderedLeafIndex l path,i)))
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun n : ℕ => (n : ZMod q))
    (bulkSamples_permuted b k l bulk top comp σ x (orderedLeafIndex l path,i))

end Ostmann.Arithmetic.CanonicalHistoryLeafBulk

end

end OAI
