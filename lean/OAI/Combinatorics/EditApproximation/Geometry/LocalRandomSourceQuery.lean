import OAI.Combinatorics.EditApproximation.Geometry.LocalGroupSourceQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A local refinement step with both kinds of random input made explicit.
All scalar group reads and range-indexed online reads precede the existing
finite earlier/current queries, whose semantic values are preserved. -/

namespace EditApproximation

section Step

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localRandomSourceStepQuery_value (oracle : ι → ℚ) (draw : CellGroupDraws M F Q)
    (integer : ℕ → TargetInterval target.length → ℕ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadGroup : ∀ key ∈ groupScalarKeys M F Q (localGroupQueryKeys N F exponent a parentInitial q),
      (readGroup key).value oracle = groupScalarValue draw key)
    (hreadInteger : ∀ key ∈ localOnlineSourceKeys N P F a parentInitial q,
      (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle =
        (integer key.1 key.2 : ℚ))
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readGroup readInteger readEarlier readCurrent).value oracle =
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
  unfold localRandomSourceStepQuery
  rw [FiniteQuery.collect_value, hvalues]
  rw [localOnlineSourceStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial child initial cached q readInteger readEarlier readCurrent oracle integer earlier current ht
    hreadInteger hreadEarlier hreadCurrent]
  unfold rationalLocalWideStep
  rw [localCellGroupActions_congr_draw source target parent N P F exponent Q tau a parentInitial
    child initial current cached draw q hdraw]

end Step

end EditApproximation

end OAI
