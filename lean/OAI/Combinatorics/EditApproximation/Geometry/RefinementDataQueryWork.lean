import OAI.Combinatorics.EditApproximation.Geometry.RefinementDataQuery
import OAI.Combinatorics.EditApproximation.Geometry.LocalRefinementQueryWork

namespace OAI

/-! Read counts for the full adaptive data query. Weighting reads permits
the same theorem to count current-index and earlier-index dependencies
separately. The bounds count executed readers, including repeated reads
across successive gathering stages. -/

namespace EditApproximation

theorem list_map_sum_le_constant {ι : Type*} (inputs : List ι) (cost : ι → ℕ) (bound : ℕ)
    (hcost : ∀ input, cost input ≤ bound) :
    (inputs.map cost).sum ≤ inputs.length * bound := by
  calc
    _ ≤ (inputs.map fun _ => bound).sum := List.sum_le_sum (fun input _ => hcost input)
    _ = _ := by simp

section BandData

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (earlier : PhysicalChildTables M target.length)
  (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
  (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
  (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
  (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
  (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2)

include ht hreadMass hreadInitial hreadEarlier hreadCurrent

theorem localRefinementBandDataQuery_cost_le (massCost initialCost earlierCost currentCost : ℕ)
    (hmassCost : ∀ input, (readMass input).cost oracle weight ≤ massCost)
    (hinitialCost : ∀ input, (readInitial input).cost oracle weight ≤ initialCost)
    (hearlierCost : ∀ input, (readEarlier input).cost oracle weight ≤ earlierCost)
    (hcurrentCost : ∀ input, (readCurrent input).cost oracle weight ≤ currentCost) :
    (localRefinementBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial draw integer q readEarlier readCurrent).cost oracle weight ≤
    (refinementBandInputList (M := M) parent N P F exponent a parentInitial q).length *
      (massCost + initialCost) +
    (queryEarlierInputCover (M := M) parent N P F exponent t a parentInitial q).card * earlierCost +
    2 * (currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
      child initial current draw q
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q)).card * currentCost := by
  let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  let mass := fun i r => finiteAnswerTable keys (keys.map fun input => child input.1 input.2) (i, r)
  let initial' := fun i r => finiteAnswerTable keys (keys.map fun input => initial input.1 input.2) (i, r)
  have hmass : ∀ input ∈ keys, mass input.1 input.2 = child input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map keys _ input hi
  have hinitial : ∀ input ∈ keys, initial' input.1 input.2 = initial input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map keys _ input hi
  have honline := localOnlineCandidates_congr_bandTables source target parent N P F exponent H
    tau a eta kappa (t - 1) parentInitial mass child initial' initial earlier integer q hmass hinitial
  have hgroups := localCellGroupActions_congr_bandTables source target parent N P F exponent Q
    tau a parentInitial mass child initial' initial current draw q hmass hinitial
  have hcover : currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
      mass initial' current draw q
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial mass initial' earlier (t - 1) integer q) =
      currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
        child initial current draw q
        (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
          parentInitial child initial earlier (t - 1) integer q) := by
    unfold currentQueryInputCover
    rw [hgroups, honline]
  have hstep := localRefinementStepQuery_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t parentInitial mass initial' draw integer q readEarlier readCurrent
    oracle weight earlier current ht hreadEarlier hreadCurrent earlierCost currentCost hearlierCost hcurrentCost
  rw [hcover] at hstep
  have hm := list_map_sum_le_constant keys (fun input => (readMass input).cost oracle weight) massCost hmassCost
  have hi := list_map_sum_le_constant keys (fun input => (readInitial input).cost oracle weight) initialCost hinitialCost
  unfold localRefinementBandDataQuery
  rw [FiniteQuery.cost_collect]
  simp only [hreadMass]
  rw [FiniteQuery.cost_collect]
  simp only [hreadInitial]
  change _ + (_ + (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial mass initial' draw integer q readEarlier readCurrent).cost oracle weight) ≤ _
  change _ ≤ keys.length * (massCost + initialCost) + _ + _
  nlinarith only [hstep, hm, hi]

end BandData

section AllData

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readParentInitial : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (earlier : PhysicalChildTables M target.length)
  (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
  (hreadParentInitial : ∀ r, (readParentInitial r).value oracle = parentInitial r)
  (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
  (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
  (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
  (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2)

include ht hreadParentInitial hreadMass hreadInitial hreadEarlier hreadCurrent

theorem localRefinementDataQuery_cost_le (parentCost massCost initialCost earlierCost currentCost : ℕ)
    (hparentCost : ∀ r, (readParentInitial r).cost oracle weight ≤ parentCost)
    (hmassCost : ∀ input, (readMass input).cost oracle weight ≤ massCost)
    (hinitialCost : ∀ input, (readInitial input).cost oracle weight ≤ initialCost)
    (hearlierCost : ∀ input, (readEarlier input).cost oracle weight ≤ earlierCost)
    (hcurrentCost : ∀ input, (readCurrent input).cost oracle weight ≤ currentCost) :
    (localRefinementDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParentInitial readMass readInitial draw integer q readEarlier readCurrent).cost oracle weight ≤
    (1 + (refinementInitialSupport N P F exponent a (parentInitial q) q).length) * parentCost +
    (refinementBandInputList (M := M) parent N P F exponent a parentInitial q).length *
      (massCost + initialCost) +
    (queryEarlierInputCover (M := M) parent N P F exponent t a parentInitial q).card * earlierCost +
    2 * (currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
      child initial current draw q
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q)).card * currentCost := by
  let keys := refinementInitialSupport N P F exponent a (parentInitial q) q
  let cached := finiteAnswerTable keys (keys.map parentInitial)
  have heq : ∀ r ∈ keys, parentInitial r = cached r := by
    intro r hr
    exact (finiteAnswerTable_map keys parentInitial r hr).symm
  have hreps := queryEarlierRepresentatives_congr_initial N P F exponent a parentInitial cached q heq
  have hearlier := queryEarlierInputCover_congr_initial (M := M) N P F exponent a parentInitial cached q heq parent t
  have hshared := querySharedInputCover_congr_initial source target parent N P F exponent Q a
    parentInitial cached draw q heq
  have hgroups := localCellGroupActions_congr_initial source target parent N P F exponent Q tau a
    parentInitial cached child initial current draw q heq
  have honline := localOnlineCandidates_congr_initial source target parent N P F exponent H
    tau a eta kappa (t - 1) parentInitial cached child initial earlier integer q heq
  have hstep := localRefinementBandDataQuery_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t cached readMass readInitial draw integer q readEarlier readCurrent
    oracle weight child initial earlier current ht hreadMass hreadInitial hreadEarlier hreadCurrent
    massCost initialCost earlierCost currentCost hmassCost hinitialCost hearlierCost hcurrentCost
  have hbandKeys : refinementBandInputList (M := M) parent N P F exponent a parentInitial q =
      refinementBandInputList parent N P F exponent a cached q := by
    unfold refinementBandInputList
    rw [hreps]
  have hcover : currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
      child initial current draw q
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) =
      currentQueryInputCover source target parent N P F exponent Q tau a cached
        child initial current draw q
        (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
          cached child initial earlier (t - 1) integer q) := by
    unfold currentQueryInputCover
    rw [hshared, hgroups, honline]
  rw [← hbandKeys, ← hearlier, ← hcover] at hstep
  have hsum := list_map_sum_le_constant keys
    (fun r => (readParentInitial r).cost oracle weight) parentCost hparentCost
  have hfirst := hparentCost q
  unfold localRefinementDataQuery
  rw [FiniteQuery.cost_bind, hreadParentInitial q, FiniteQuery.cost_collect]
  simp only [hreadParentInitial]
  change _ + (_ + (localRefinementBandDataQuery source target parent N P F exponent H Q
    tau a eta kappa delta t cached readMass readInitial draw integer q readEarlier readCurrent).cost oracle weight) ≤ _
  change _ ≤ (1 + keys.length) * parentCost + _ + _ + _
  nlinarith only [hstep, hsum, hfirst]

end AllData

section Keys

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (readParent : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (predicate : ι → Prop)

theorem localRefinementStepQuery_keys_all
    (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → predicate key)
    (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → predicate key) :
    ∀ key ∈ (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).keys oracle, predicate key := by
  unfold localRefinementStepQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hearlier input key hk
  · intro earlierValues
    apply FiniteQuery.keys_all_collect
    · intro input _ key hk
      exact hcurrent input key hk
    · intro sharedValues
      apply FiniteQuery.keys_all_collect
      · intro input _ key hk
        exact hcurrent input key hk
      · intro currentValues key hk
        exact False.elim (List.not_mem_nil hk)

theorem localRefinementBandDataQuery_keys_all
    (hmass : ∀ input key, key ∈ (readMass input).keys oracle → predicate key)
    (hinitial : ∀ input key, key ∈ (readInitial input).keys oracle → predicate key)
    (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → predicate key)
    (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → predicate key) :
    ∀ key ∈ (localRefinementBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial draw integer q readEarlier readCurrent).keys oracle, predicate key := by
  unfold localRefinementBandDataQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hmass input key hk
  · intro massValues
    apply FiniteQuery.keys_all_collect
    · intro input _ key hk
      exact hinitial input key hk
    · intro initialValues
      exact localRefinementStepQuery_keys_all source target parent N P F exponent H Q
        tau a eta kappa delta t parentInitial _ _ draw integer q readEarlier readCurrent
        oracle predicate hearlier hcurrent

theorem localRefinementDataQuery_keys_all
    (hparent : ∀ r key, key ∈ (readParent r).keys oracle → predicate key)
    (hmass : ∀ input key, key ∈ (readMass input).keys oracle → predicate key)
    (hinitial : ∀ input key, key ∈ (readInitial input).keys oracle → predicate key)
    (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → predicate key)
    (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → predicate key) :
    ∀ key ∈ (localRefinementDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParent readMass readInitial draw integer q readEarlier readCurrent).keys oracle, predicate key := by
  unfold localRefinementDataQuery
  rw [FiniteQuery.keys_bind]
  intro key hk
  rcases List.mem_append.mp hk with hfirst | hrest
  · exact hparent q key hfirst
  · apply FiniteQuery.keys_all_collect oracle predicate readParent
      (refinementInitialSupport N P F exponent a ((readParent q).value oracle) q) _ ?_ ?_ key hrest
    · intro r _ other ho
      exact hparent r other ho
    · intro initialValues
      exact localRefinementBandDataQuery_keys_all source target parent N P F exponent H Q
        tau a eta kappa delta t _ readMass readInitial draw integer q readEarlier readCurrent
        oracle predicate hmass hinitial hearlier hcurrent

end Keys

end EditApproximation

end OAI
