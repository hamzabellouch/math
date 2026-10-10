import OAI.Combinatorics.EditApproximation.Binary.BinaryBandGuardWork
import OAI.Combinatorics.EditApproximation.Numerics.RationalWideStep
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Stored-fraction execution of the Bellman and refinement continuations.
The action lists and child entries have already been gathered; the routines
below perform every numerical operation returning the next table value. -/

namespace EditApproximation



def BinaryBellmanAction.decode {Parent Child : Type*} {M : ℕ}
    (action : BinaryBellmanAction Parent Child M) : RationalBellmanAction Parent Child M :=
  ⟨action.center, action.connection.value, action.childState⟩

namespace BinaryFraction

open Finset

def bellmanActionWithWork {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (action : BinaryBellmanAction Parent Child M) :
    BinaryFraction × ℕ :=
  let dist := distance query action.center
  let spatial := canonicalMulWithWork L dist.1
  let connection := canonicalAddWithWork spatial.1 action.connection
  let children := sumListWithWork (List.ofFn fun i => child (action.childState i))
  let result := canonicalAddWithWork connection.1 children.1
  (result.1, dist.2 + spatial.2 + connection.2 + children.2 + result.2 + 3)

@[simp] theorem bellmanActionWithWork_value {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (action : BinaryBellmanAction Parent Child M) :
    (bellmanActionWithWork distance L child query action).1.value =
      rationalActionValue (fun q r => (distance q r).1.value) L.value
        (fun s => (child s).value) query action.decode := by
  simp only [bellmanActionWithWork, canonicalAddWithWork_value, canonicalMulWithWork_value,
    sumListWithWork_value, List.map_ofFn, List.sum_ofFn, rationalActionValue, BinaryBellmanAction.decode, Function.comp_def]

def bellmanActionWordBudget (M B : ℕ) : ℕ :=
  8 * (40 * B + 22 + bandMassTotalStorageBudget M B) + 6

def bellmanActionBitBudget (M B C : ℕ) : ℕ :=
  C + 2000 * (B + 1) ^ 2 + 6000 * (5 * B + 3) ^ 2 + storedSumBitBudget M B + 6 * M +
    6000 * (40 * B + 22 + bandMassTotalStorageBudget M B + 1) ^ 2 + 3

theorem bellmanActionWithWork_bounds {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (action : BinaryBellmanAction Parent Child M)
    (B C : ℕ) (hL : L.width ≤ B) (hd : (distance query action.center).1.width ≤ B)
    (hdc : (distance query action.center).2 ≤ C) (hconn : action.connection.width ≤ B)
    (hchild : ∀ i, (child (action.childState i)).width ≤ B) :
    (bellmanActionWithWork distance L child query action).1.width ≤ bellmanActionWordBudget M B ∧
    (bellmanActionWithWork distance L child query action).2 ≤ bellmanActionBitBudget M B C := by
  have hsw := canonicalMulWithWork_width L (distance query action.center).1 B hL hd
  have hsc := canonicalMulWithWork_cost L (distance query action.center).1 B hL hd
  have hcw := canonicalAddWithWork_width (canonicalMulWithWork L (distance query action.center).1).1
    action.connection (5 * B + 2) (by omega) (by omega)
  have hcc := canonicalAddWithWork_cost (canonicalMulWithWork L (distance query action.center).1).1
    action.connection (5 * B + 2) (by omega) (by omega)
  have hlist : ∀ a ∈ (List.ofFn fun i => child (action.childState i)), a.width ≤ B := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hchild i
  have htw := sumListWithWork_width _ B hlist
  have htc := sumListWithWork_cost _ B hlist
  simp only [List.length_ofFn] at htw htc
  have htotalw := canonicalAddWithWork_width
    (canonicalAddWithWork (canonicalMulWithWork L (distance query action.center).1).1 action.connection).1
    (sumListWithWork (List.ofFn fun i => child (action.childState i))).1
    (40 * B + 22 + bandMassTotalStorageBudget M B) (by omega) (by omega)
  have htotalc := canonicalAddWithWork_cost
    (canonicalAddWithWork (canonicalMulWithWork L (distance query action.center).1).1 action.connection).1
    (sumListWithWork (List.ofFn fun i => child (action.childState i))).1
    (40 * B + 22 + bandMassTotalStorageBudget M B) (by omega) (by omega)
  constructor
  · exact htotalw
  · simp only [Nat.add_assoc, Nat.reduceAdd] at hcc
    change _ + _ + _ + _ + _ + 3 ≤ _
    unfold bellmanActionBitBudget
    omega

def bellmanWithWork {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (actions : List (BinaryBellmanAction Parent Child M)) :
    BinaryFraction × ℕ :=
  let scores := arithmeticMapWithWork (bellmanActionWithWork distance L child query) actions
  let result := minimumWithWork fallback scores.1
  (result.1, scores.2 + result.2 + 1)

@[simp] theorem bellmanWithWork_value {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (actions : List (BinaryBellmanAction Parent Child M)) :
    (bellmanWithWork distance L fallback child query actions).1.value =
      rationalBellman (fun _ => fallback.value) (fun q r => (distance q r).1.value) L.value
        (actions.map BinaryBellmanAction.decode) (fun s => (child s).value) query := by
  simp only [bellmanWithWork, minimumWithWork_value, arithmeticMapWithWork_value, List.map_map,
    Function.comp_def, bellmanActionWithWork_value, rationalBellman]

def bellmanBitBudget (M n B F C : ℕ) : ℕ :=
  n * (bellmanActionBitBudget M B C + 3) +
    (1 + n * (1000 * (F + bellmanActionWordBudget M B + 1) ^ 2 + 2)) + 1

theorem bellmanWithWork_bounds {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (actions : List (BinaryBellmanAction Parent Child M))
    (B F C : ℕ) (hL : L.width ≤ B) (hf : fallback.width ≤ F)
    (hd : ∀ action ∈ actions, (distance query action.center).1.width ≤ B)
    (hdc : ∀ action ∈ actions, (distance query action.center).2 ≤ C)
    (hc : ∀ action ∈ actions, action.connection.width ≤ B)
    (hv : ∀ action ∈ actions, ∀ i, (child (action.childState i)).width ≤ B) :
    (bellmanWithWork distance L fallback child query actions).1.width ≤ F + bellmanActionWordBudget M B ∧
      (bellmanWithWork distance L fallback child query actions).2 ≤ bellmanBitBudget M actions.length B F C := by
  let scores := arithmeticMapWithWork (bellmanActionWithWork distance L child query) actions
  have hs (value : BinaryFraction) (hvalue : value ∈ scores.1) : value.width ≤ bellmanActionWordBudget M B := by
    simp only [scores, arithmeticMapWithWork_value] at hvalue
    obtain ⟨action, ha, heq⟩ := List.mem_map.mp hvalue
    subst value
    exact (bellmanActionWithWork_bounds distance L child query action B C hL
      (hd action ha) (hdc action ha) (hc action ha) (hv action ha)).1
  have hlen : scores.1.length = actions.length := by
    simp only [scores, arithmeticMapWithWork_value, List.length_map]
  have hmap := arithmeticMapWithWork_cost (bellmanActionWithWork distance L child query) actions
    (bellmanActionBitBudget M B C) (fun action ha =>
      (bellmanActionWithWork_bounds distance L child query action B C hL
        (hd action ha) (hdc action ha) (hc action ha) (hv action ha)).2)
  have hminw := minimumWithWork_width fallback scores.1 (F + bellmanActionWordBudget M B)
    (by omega) (fun value hv => (hs value hv).trans (by omega))
  have hminc := minimumWithWork_cost fallback scores.1 (F + bellmanActionWordBudget M B)
    (by omega) (fun value hv => (hs value hv).trans (by omega))
  rw [hlen] at hminc
  refine ⟨hminw, ?_⟩
  change scores.2 + (minimumWithWork fallback scores.1).2 + 1 ≤ _
  change scores.2 ≤ _ at hmap
  unfold bellmanBitBudget
  omega



@[simp] theorem onlineMinimumWithWork_value (values : List BinaryFraction) :
    ((onlineMinimumWithWork values).1.map value) = rationalOnlineMinimum (values.map value) := by
  cases values with
  | nil => rfl
  | cons first rest => simp only [onlineMinimumWithWork, Option.map_some, minimumWithWork_value,
      rationalOnlineMinimum, List.map_cons]

theorem onlineMinimumWithWork_bounds (values : List BinaryFraction) (B : ℕ)
    (hv : ∀ value ∈ values, value.width ≤ B) :
    (∀ value ∈ (onlineMinimumWithWork values).1, value.width ≤ B) ∧
      (onlineMinimumWithWork values).2 ≤ 2 + values.length * (1000 * (B + 1) ^ 2 + 2) := by
  cases values with
  | nil =>
    constructor
    · simp [onlineMinimumWithWork]
    · change 1 ≤ 2 + 0 * _
      omega
  | cons head rest =>
    have hw := minimumWithWork_width head rest B (hv head (by simp))
      (fun value h => hv value (by simp [h]))
    have hc := minimumWithWork_cost head rest B (hv head (by simp))
      (fun value h => hv value (by simp [h]))
    constructor
    · intro value hvalue
      have heq : value = (minimumWithWork head rest).1 := by simpa only [onlineMinimumWithWork,
        Option.mem_def, Option.some.injEq] using hvalue.symm
      exact heq ▸ hw
    · change _ + 1 ≤ _
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega



@[simp] theorem refinementUpdateWithWork_value (delta cone : BinaryFraction) (online : Option BinaryFraction) :
    (refinementUpdateWithWork delta cone online).1.value =
      rationalRefinementUpdate delta.value cone.value (online.map value) := by
  cases online with
  | none => rfl
  | some online =>
    simp only [refinementUpdateWithWork, minWithWork_value, maxWithWork_value,
      divWithWork_value, canonicalAddWithWork_value, one, nat_value,
      Nat.cast_one, Option.map_some, rationalRefinementUpdate]

def refinementUpdateWordBudget (B : ℕ) : ℕ := 32 * B + 28

def refinementUpdateBitBudget (B : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + 2100 * (8 * B + 8) ^ 2 +
    2 * (1000 * (32 * B + 29) ^ 2 + 1) + 2

theorem refinementUpdateWithWork_bounds (delta cone : BinaryFraction) (online : Option BinaryFraction)
    (B : ℕ) (hB : 1 ≤ B) (hd : delta.width ≤ B) (hc : cone.width ≤ B)
    (ho : ∀ a ∈ online, a.width ≤ B) :
    (refinementUpdateWithWork delta cone online).1.width ≤ refinementUpdateWordBudget B ∧
    (refinementUpdateWithWork delta cone online).2 ≤ refinementUpdateBitBudget B := by
  cases online with
  | none =>
    refine ⟨?_, ?_⟩
    · change cone.width ≤ _
      unfold refinementUpdateWordBudget
      omega
    · change 1 ≤ _
      unfold refinementUpdateBitBudget
      omega
  | some online =>
    have hwone : one.width ≤ B := by change 1 ≤ B; exact hB
    have hdw := canonicalAddWithWork_width one delta B hwone hd
    have hdc := canonicalAddWithWork_cost one delta B hwone hd
    have hlw := divWithWork_width_uniform cone (canonicalAddWithWork one delta).1 (8 * B + 6)
      (by omega) hdw
    have hlc := divWithWork_cost cone (canonicalAddWithWork one delta).1 (8 * B + 6)
      (by omega) hdw
    have how : online.width ≤ B := ho online (by simp)
    have hmaxw := maxWithWork_width (divWithWork cone (canonicalAddWithWork one delta).1).1 online
    have hmaxc := maxWithWork_cost (divWithWork cone (canonicalAddWithWork one delta).1).1 online
      (32 * B + 28) (by omega) (by omega)
    have hminw := minWithWork_width cone (maxWithWork
      (divWithWork cone (canonicalAddWithWork one delta).1).1 online).1
    have hminc := minWithWork_cost cone (maxWithWork
      (divWithWork cone (canonicalAddWithWork one delta).1).1 online).1 (32 * B + 28)
      (by omega) (by omega)
    constructor
    · change (minWithWork cone (maxWithWork
        (divWithWork cone (canonicalAddWithWork one delta).1).1 online).1).1.width ≤ refinementUpdateWordBudget B
      unfold refinementUpdateWordBudget
      omega
    · simp only [Nat.add_assoc, Nat.reduceAdd] at hlc hmaxc hminc
      change _ + _ + _ + _ + 2 ≤ _
      unfold refinementUpdateBitBudget
      omega

/-- Numerical tail of the actual local refinement query, after its finite
wide, group and online lists have been prepared from gathered data. -/
def localContinuationWithWork {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L delta fallback : BinaryFraction)
    (old current : Child → BinaryFraction) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M)) : BinaryFraction × ℕ :=
  let warm := bellmanWithWork distance L fallback old query wide
  let cone := bellmanWithWork distance L warm.1 current query groups
  let scores := arithmeticMapWithWork (bellmanActionWithWork distance L current query) online
  let onlineMin := onlineMinimumWithWork scores.1
  let result := refinementUpdateWithWork delta cone.1 onlineMin.1
  (result.1, warm.2 + cone.2 + scores.2 + onlineMin.2 + result.2 + 3)

@[simp] theorem localContinuationWithWork_value {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L delta fallback : BinaryFraction)
    (old current : Child → BinaryFraction) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M)) :
    (localContinuationWithWork distance L delta fallback old current query wide groups online).1.value =
      rationalRefinementUpdate delta.value
        (rationalMinimum
          (rationalBellman (fun _ => fallback.value) (fun q r => (distance q r).1.value) L.value
            (wide.map BinaryBellmanAction.decode) (fun s => (old s).value) query)
          ((groups.map BinaryBellmanAction.decode).map
            (rationalActionValue (fun q r => (distance q r).1.value) L.value (fun s => (current s).value) query)))
        (rationalOnlineMinimum ((online.map BinaryBellmanAction.decode).map
          (rationalActionValue (fun q r => (distance q r).1.value) L.value (fun s => (current s).value) query))) := by
  simp only [localContinuationWithWork, refinementUpdateWithWork_value, bellmanWithWork_value,
    onlineMinimumWithWork_value, arithmeticMapWithWork_value, List.map_map, Function.comp_def,
    bellmanActionWithWork_value, rationalBellman]

end BinaryFraction
end EditApproximation

end OAI
