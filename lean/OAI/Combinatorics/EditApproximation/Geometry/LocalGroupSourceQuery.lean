import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineSourceQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Whole-cell group samples are exposed through scalar source reads.
Every needed scale/sample coordinate is enumerated once per group; unused
groups are absent from this query. -/

namespace EditApproximation





theorem groupScalarKeys_mem (M F Q : ℕ) (groups : List (ℕ × (ℕ × ℕ)))
    (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups)
    (scale : Fin (groupDyadicScales M key.1 F).length)
    (sample : Fin (groupSampleCount M Q key.1 (groupDyadicScaleAt M key.1 F scale))) :
    (⟨key, scale, sample⟩ : GroupScalarKey M F Q) ∈ groupScalarKeys M F Q groups := by
  apply List.mem_flatMap.mpr
  refine ⟨key, hk, List.mem_flatMap.mpr ?_⟩
  exact ⟨scale, List.mem_finRange _, List.mem_map.mpr ⟨sample, List.mem_finRange _, rfl⟩⟩

theorem groupScalarKeys_length_le (M F Q labels : ℕ) (groups : List (ℕ × (ℕ × ℕ)))
    (hlabels : ∀ key ∈ groups, (groupDyadicScales M key.1 F).length ≤ labels) :
    (groupScalarKeys M F Q groups).length ≤ groups.length * labels * M := by
  have hgroup (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups) :
      ((List.finRange (groupDyadicScales M key.1 F).length).flatMap fun scale =>
        (List.finRange (groupSampleCount M Q key.1 (groupDyadicScaleAt M key.1 F scale))).map
          fun sample => (⟨key, scale, sample⟩ : GroupScalarKey M F Q)).length ≤ labels * M := by
    apply le_trans (list_flatMap_length_le _ _ M ?_) ?_
    · intro scale _
      simp only [List.length_map, List.length_finRange]
      exact min_le_left _ _
    · simpa only [List.length_finRange] using Nat.mul_le_mul_right M (hlabels key hk)
  calc
    _ ≤ groups.length * (labels * M) := list_flatMap_length_le _ _ _ hgroup
    _ = _ := by ring

def groupScalarValue {M F Q : ℕ} (draw : CellGroupDraws M F Q) (key : GroupScalarKey M F Q) : ℚ :=
  (draw key.1.1 key.1.2 key.2.1 key.2.2).val



theorem groupDrawFromValues_eq {M F Q : ℕ} [NeZero M]
    (groups : List (ℕ × (ℕ × ℕ))) (draw : CellGroupDraws M F Q)
    (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups) :
    groupDrawFromValues (groupScalarKeys M F Q groups)
        ((groupScalarKeys M F Q groups).map (groupScalarValue draw)) key.1 key.2 = draw key.1 key.2 := by
  classical
  funext scale sample
  apply Fin.ext
  simp only [groupDrawFromValues, Fin.val_ofNat]
  rw [finiteAnswerTable_map _ _ _ (groupScalarKeys_mem M F Q groups key hk scale sample)]
  simp only [groupScalarValue, Nat.floor_natCast]
  exact Nat.mod_eq_of_lt (draw key.1 key.2 scale sample).isLt

theorem localCellGroupActions_congr_draw {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
    (initial : TargetInterval target.length → ℚ)
    (child warmup current : Fin M → TargetInterval target.length → ℚ)
    (left right : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (h : ∀ key ∈ localGroupQueryKeys N F exponent a initial q, left key.1 key.2 = right key.1 key.2) :
    localCellGroupActions source target parent N P F exponent Q tau a initial child warmup current left q =
      localCellGroupActions source target parent N P F exponent Q tau a initial child warmup current right q := by
  unfold localCellGroupActions
  apply List.flatMap_congr
  intro b hb
  apply List.filterMap_congr
  intro cell hc
  rw [h (b, cell) (List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨cell, hc, rfl⟩⟩)]

section Query

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

noncomputable def localGroupSourceStepQuery : FiniteQuery ι :=
  let keys := groupScalarKeys M F Q (localGroupQueryKeys N F exponent a parentInitial q)
  FiniteQuery.collect readGroup keys fun values =>
    localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial (groupDrawFromValues keys values) integer q readEarlier readCurrent

theorem localGroupSourceStepQuery_value (oracle : ι → ℚ) (draw : CellGroupDraws M F Q)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadGroup : ∀ key ∈ groupScalarKeys M F Q (localGroupQueryKeys N F exponent a parentInitial q),
      (readGroup key).value oracle = groupScalarValue draw key)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localGroupSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial integer q readGroup readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  classical
  let groups := localGroupQueryKeys N F exponent a parentInitial q
  let keys := groupScalarKeys M F Q groups
  have hvalues : keys.map (fun key => (readGroup key).value oracle) = keys.map (groupScalarValue draw) := by
    apply List.map_congr_left
    intro key hk
    exact hreadGroup key hk
  let cached := groupDrawFromValues keys (keys.map (groupScalarValue draw))
  have hdraw : ∀ key ∈ groups, cached key.1 key.2 = draw key.1 key.2 :=
    fun key hk => groupDrawFromValues_eq groups draw key hk
  unfold localGroupSourceStepQuery
  rw [FiniteQuery.collect_value, hvalues]
  rw [localRefinementStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial child initial cached integer q readEarlier readCurrent oracle earlier current ht
    hreadEarlier hreadCurrent]
  unfold rationalLocalWideStep
  rw [localCellGroupActions_congr_draw source target parent N P F exponent Q tau a parentInitial
    child initial current cached draw q hdraw]

end Query

end EditApproximation

end OAI
