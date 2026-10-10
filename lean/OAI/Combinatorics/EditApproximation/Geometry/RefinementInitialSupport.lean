import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmupStepQuery
import OAI.Combinatorics.EditApproximation.Geometry.LocalRefinementQuery
import OAI.Combinatorics.EditApproximation.Geometry.BandEarlierDependence
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Finite initial-table support for the literal refinement loops. The
query value determines the raw local lists; tests of other initial values
only remove elements from these lists. -/

namespace EditApproximation



theorem refinementInitialSupport_query {n : ℕ} (N P F exponent : ℕ) (a value : ℚ)
    (q : TargetInterval n) : q ∈ refinementInitialSupport N P F exponent a value q :=
  List.mem_cons_self

theorem refinementInitialSupport_local {n : ℕ} (N P F exponent : ℕ) (a value : ℚ)
    (q r : TargetInterval n) (hr : r ∈ rawRefinementCenters N P F a value q) :
    r ∈ refinementInitialSupport N P F exponent a value q := by
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hr))

theorem localGroupQueryKeys_congr_initial {n : ℕ} (N F exponent : ℕ) (a : ℚ)
    (left right : TargetInterval n → ℚ) (q : TargetInterval n) (hq : left q = right q) :
    localGroupQueryKeys N F exponent a left q = localGroupQueryKeys N F exponent a right q := by
  simp only [localGroupQueryKeys, hq]

theorem refinementInitialSupport_cell {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (key : ℕ × (ℕ × ℕ))
    (hk : key ∈ localGroupQueryKeys N F exponent a initial q) (r : TargetInterval n)
    (hr : r ∈ cellTargetStates n (seedGridSpacing key.1 P)
      ((2 : ℚ) ^ (-(exponent : ℤ)) * key.1) key.2) :
    r ∈ refinementInitialSupport N P F exponent a (initial q) q := by
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨key, ?_, hr⟩
  simpa only [localGroupQueryKeys] using hk

theorem refinementInitialSupport_online {n : ℕ} (N P F exponent : ℕ) (a value : ℚ)
    (q : TargetInterval n) (b : ℕ) (hb : b ∈ dyadicQueryWindow N value a F) :
    roundInterval (seedGridSpacing b P) q ∈ refinementInitialSupport N P F exponent a value q := by
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨b, hb, rfl⟩

theorem cellRepresentativeStates_congr_initial {n : ℕ} (P F b : ℕ) (a theta : ℚ)
    (left right : TargetInterval n → ℚ) (cell : ℕ × ℕ)
    (heq : ∀ r ∈ cellTargetStates n (seedGridSpacing b P) (theta * b) cell,
      left r = right r) :
    cellRepresentativeStates n P F b a left theta cell =
      cellRepresentativeStates n P F b a right theta cell := by
  unfold cellRepresentativeStates
  apply List.filter_congr
  intro r hr
  rw [heq r hr]

section ParentTable

variable {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
  (left right : TargetInterval n → ℚ) (q : TargetInterval n)
  (heq : ∀ r ∈ refinementInitialSupport N P F exponent a (left q) q, left r = right r)

include heq

theorem refinement_local_representatives_congr :
    localRefinementRepresentatives N P F a left q = localRefinementRepresentatives N P F a right q := by
  apply localRefinementRepresentatives_congr_raw
  · exact heq q (refinementInitialSupport_query N P F exponent a (left q) q)
  · intro r hr
    exact heq r (refinementInitialSupport_local N P F exponent a (left q) q r hr)

theorem refinement_cell_representatives_congr (key : ℕ × (ℕ × ℕ))
    (hk : key ∈ localGroupQueryKeys N F exponent a left q) :
    cellRepresentativeStates n P F key.1 a left ((2 : ℚ) ^ (-(exponent : ℤ))) key.2 =
      cellRepresentativeStates n P F key.1 a right ((2 : ℚ) ^ (-(exponent : ℤ))) key.2 := by
  apply cellRepresentativeStates_congr_initial
  intro r hr
  exact heq r (refinementInitialSupport_cell N P F exponent a left q key hk r hr)

theorem queryEarlierRepresentatives_congr_initial :
    queryEarlierRepresentatives N P F exponent a left q =
      queryEarlierRepresentatives N P F exponent a right q := by
  have hq := heq q (refinementInitialSupport_query N P F exponent a (left q) q)
  have hkeys := localGroupQueryKeys_congr_initial N F exponent a left right q hq
  unfold queryEarlierRepresentatives
  rw [refinement_local_representatives_congr N P F exponent a left right q heq, ← hkeys, ← hq]
  congr 2
  apply List.flatMap_congr
  intro key hk
  rw [refinement_cell_representatives_congr N P F exponent a left right q heq key hk]

theorem queryEarlierInputCover_congr_initial {nx M : ℕ} (parent : TargetInterval nx) (history : ℕ) :
    queryEarlierInputCover (M := M) parent N P F exponent history a left q =
      queryEarlierInputCover parent N P F exponent history a right q := by
  unfold queryEarlierInputCover
  rw [queryEarlierRepresentatives_congr_initial N P F exponent a left right q heq]

end ParentTable

section Programs

variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa : ℚ) (t : ℕ)
  (left right : TargetInterval target.length → ℚ)
  (child initial current : Fin M → TargetInterval target.length → ℚ)
  (children : PhysicalChildTables M target.length)
  (integer : ℕ → TargetInterval target.length → ℕ) (draw : CellGroupDraws M F Q)
  (q : TargetInterval target.length)
  (heq : ∀ r ∈ refinementInitialSupport N P F exponent a (left q) q, left r = right r)

include heq

theorem localOnlineCandidates_congr_initial :
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      left child initial children t integer q =
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      right child initial children t integer q := by
  have hq := heq q (refinementInitialSupport_query N P F exponent a (left q) q)
  unfold localOnlineCandidates
  rw [← hq]
  apply List.filterMap_congr
  intro b hb
  dsimp only
  rw [heq _ (refinementInitialSupport_online N P F exponent a (left q) q b hb)]

theorem localCellGroupActions_congr_initial :
    localCellGroupActions source target parent N P F exponent Q tau a left child initial current draw q =
      localCellGroupActions source target parent N P F exponent Q tau a right child initial current draw q := by
  have hq := heq q (refinementInitialSupport_query N P F exponent a (left q) q)
  unfold localCellGroupActions
  rw [← hq]
  apply List.flatMap_congr
  intro b hb
  apply List.filterMap_congr
  intro cell hc
  unfold chooseCellGroupAction cellUnskippedBands
  rw [refinement_cell_representatives_congr N P F exponent a left right q heq (b, cell)
    (List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨cell, hc, rfl⟩⟩)]

theorem querySharedInputCover_congr_initial :
    querySharedInputCover source target parent N F exponent Q a left q draw =
      querySharedInputCover source target parent N F exponent Q a right q draw := by
  unfold querySharedInputCover
  rw [localGroupQueryKeys_congr_initial N F exponent a left right q
    (heq q (refinementInitialSupport_query N P F exponent a (left q) q))]

theorem rationalLocalWideStep_congr_initial (delta : ℚ)
    (old : Fin M → TargetInterval target.length → ℚ)
    (online : List (PhysicalRationalAction M target.length)) :
    rationalLocalWideStep source target parent N P F exponent Q tau a delta left
      child initial old current draw online q =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta right
      child initial old current draw online q := by
  have hgroups := localCellGroupActions_congr_initial source target parent N P F exponent Q tau a
    left right child initial current draw q heq
  have hreps := refinement_local_representatives_congr N P F exponent a left right q heq
  have hq := heq q (refinementInitialSupport_query N P F exponent a (left q) q)
  unfold rationalLocalWideStep
  rw [hgroups, hreps]
  unfold rationalBellman
  rw [hq]

end Programs

section Query

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readInitial : TargetInterval target.length → FiniteQuery ι)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

/-- First gather the finite parent initial data that select all later
representative and cell lists. Child mass/initial data are gathered by a
separate layer, independently of the current-index reads. -/
def localRefinementInitialQuery : FiniteQuery ι :=
  FiniteQuery.bind (readInitial q) fun value =>
    let keys := refinementInitialSupport N P F exponent a value q
    FiniteQuery.collect readInitial keys fun answers =>
      localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        (finiteAnswerTable keys answers) child initial draw integer q readEarlier readCurrent

theorem localRefinementInitialQuery_value (oracle : ι → ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadInitial : ∀ r, (readInitial r).value oracle = parentInitial r)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRefinementInitialQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readInitial child initial draw integer q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  let keys := refinementInitialSupport N P F exponent a (parentInitial q) q
  let cached := finiteAnswerTable keys (keys.map parentInitial)
  have heq : ∀ r ∈ refinementInitialSupport N P F exponent a (parentInitial q) q,
      parentInitial r = cached r := by
    intro r hr
    exact (finiteAnswerTable_map keys parentInitial r hr).symm
  have honline := localOnlineCandidates_congr_initial source target parent N P F exponent H
    tau a eta kappa (t - 1) parentInitial cached child initial earlier integer q heq
  have hstep := rationalLocalWideStep_congr_initial source target parent N P F exponent Q tau a
    parentInitial cached child initial current draw q heq delta (fun i r => earlier i (t - 1) r)
    (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial earlier (t - 1) integer q)
  unfold localRefinementInitialQuery
  rw [FiniteQuery.bind_value, hreadInitial q, FiniteQuery.collect_value]
  simp only [hreadInitial]
  rw [localRefinementStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    cached child initial draw integer q readEarlier readCurrent oracle earlier current ht
    hreadEarlier hreadCurrent]
  rw [← honline]
  exact hstep.symm

end Query

end EditApproximation

end OAI
