import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveLeafExpansion
import OAI.NumberTheory.Ostmann.Characters.QuartetIndexCoordinates

namespace OAI

/-! # The actual transfer has opposite conjugations in every bottom sibling pair -/

namespace Ostmann

/-- `true` means complex conjugation, as in `rationalTreeAmplitude`. -/
def transferConjugations : (n : ℕ) → Bool → TreeLeafTuple Bool n
  | 0, b => b
  | n + 1, b => (transferConjugations n b, transferConjugations n (!b))

def transferConjugationList : ℕ → Bool → List Bool
  | 0, b => [b]
  | n + 1, b => transferConjugationList n b ++ transferConjugationList n (!b)

theorem transferConjugationList_flip (n : ℕ) (b : Bool) :
    transferConjugationList n (!b) = (transferConjugationList n b).map Bool.not := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [transferConjugationList, List.map_append, ← ih]

theorem transferLeafList_flags {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    (transferLeafList sys n σ t).map Prod.snd = transferConjugationList n true := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [transferLeafList, List.map_append]
    have hm (l : List ((State × ℤ) × Bool)) :
        (l.map (fun z => (z.1, !z.2))).map Prod.snd =
          (l.map Prod.snd).map Bool.not := by simp only [List.map_map, Function.comp_def]
    rw [hm, ih, ih, ← transferConjugationList_flip]
    rfl

theorem transferLeafList_conjugations {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    (transferLeafList sys n σ t).map (fun z => !z.2) = transferConjugationList n false := by
  rw [show (fun z : (State × ℤ) × Bool => !z.2) = Bool.not ∘ Prod.snd from rfl,
    ← List.map_map, transferLeafList_flags, ← transferConjugationList_flip]
  rfl

def treeLeafTupleList {A : Type*} : (n : ℕ) → TreeLeafTuple A n → List A
  | 0, a => [a]
  | n + 1, a => treeLeafTupleList n a.1 ++ treeLeafTupleList n a.2

theorem transferConjugations_list (n : ℕ) (b : Bool) :
    treeLeafTupleList n (transferConjugations n b) = transferConjugationList n b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [transferConjugations, treeLeafTupleList, transferConjugationList, ih]

theorem transferConjugations_quartet (n : ℕ) (b : Bool) (q : TreeLeafIndex n) :
    quartetBlockEquiv Bool n (transferConjugations (n + 2) b) q =
      let c := treeLeafTupleEquiv Bool n (transferConjugations n b) q
      ((c, !c), (!c, c)) := by
  induction n generalizing b with
  | zero => cases q; cases b <;> rfl
  | succ n ih =>
    cases q with
    | inl q => exact ih b q
    | inr q => exact ih (!b) q

end Ostmann

end OAI
