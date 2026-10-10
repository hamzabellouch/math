import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomDataQuery
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryRestriction
import OAI.Combinatorics.EditApproximation.Geometry.RefinementDataQueryWork

namespace OAI

namespace EditApproximation

namespace FiniteQuery

theorem keys_all_mapKeys {ι κ : Type*} (f : ι → κ) (query : FiniteQuery ι)
    (oracle : κ → ℚ) (predicate : κ → Prop)
    (h : ∀ key ∈ query.keys (oracle ∘ f), predicate (f key)) :
    ∀ key ∈ (mapKeys f query).keys oracle, predicate key := by
  rw [mapKeys_keys]
  intro key hk
  obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
  exact h other ho

end FiniteQuery

section Keys

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (readParent : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (predicate : ι → Prop)

variable
  (hgroup : ∀ input key, key ∈ (readGroup input).keys oracle → predicate key)
  (hinteger : ∀ input range key, key ∈ (readInteger input range).keys oracle → predicate key)
  (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → predicate key)
  (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → predicate key)

omit [NeZero M] in
include hinteger hearlier hcurrent in
 theorem localOnlineSourceStepQuery_keys_all (draw : CellGroupDraws M F Q) :
    ∀ key ∈ (localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw q readInteger readEarlier readCurrent).keys oracle, predicate key := by
  unfold localOnlineSourceStepQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hinteger input _ key hk
  · intro values
    exact localRefinementStepQuery_keys_all source target parent N P F exponent H Q
      tau a eta kappa delta t parentInitial child initial draw _ q readEarlier readCurrent
      oracle predicate hearlier hcurrent

include hgroup hinteger hearlier hcurrent in
 theorem localRandomSourceStepQuery_keys_all :
    ∀ key ∈ (localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readGroup readInteger readEarlier readCurrent).keys oracle, predicate key := by
  unfold localRandomSourceStepQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hgroup input key hk
  · intro values
    exact localOnlineSourceStepQuery_keys_all source target parent N P F exponent H Q
      tau a eta kappa delta t parentInitial child initial readInteger q readEarlier readCurrent
      oracle predicate hinteger hearlier hcurrent _

include hgroup hinteger hearlier hcurrent in
 theorem localRandomBandDataQuery_keys_all
    (hmass : ∀ input key, key ∈ (readMass input).keys oracle → predicate key)
    (hinitial : ∀ input key, key ∈ (readInitial input).keys oracle → predicate key) :
    ∀ key ∈ (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).keys oracle,
      predicate key := by
  unfold localRandomBandDataQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hmass input key hk
  · intro massValues
    apply FiniteQuery.keys_all_collect
    · intro input _ key hk
      exact hinitial input key hk
    · intro initialValues
      exact localRandomSourceStepQuery_keys_all source target parent N P F exponent H Q
        tau a eta kappa delta t parentInitial _ _ readGroup readInteger q readEarlier readCurrent
        oracle predicate hgroup hinteger hearlier hcurrent

include hgroup hinteger hearlier hcurrent in
 theorem localRandomDataQuery_keys_all
    (hparent : ∀ r key, key ∈ (readParent r).keys oracle → predicate key)
    (hmass : ∀ input key, key ∈ (readMass input).keys oracle → predicate key)
    (hinitial : ∀ input key, key ∈ (readInitial input).keys oracle → predicate key) :
    ∀ key ∈ (localRandomDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).keys oracle,
      predicate key := by
  unfold localRandomDataQuery
  rw [FiniteQuery.keys_bind]
  intro key hk
  rcases List.mem_append.mp hk with hfirst | hrest
  · exact hparent q key hfirst
  · apply FiniteQuery.keys_all_collect oracle predicate readParent
      (refinementInitialSupport N P F exponent a ((readParent q).value oracle) q) _ ?_ ?_ key hrest
    · intro r _ other ho
      exact hparent r other ho
    · intro initialValues
      exact localRandomBandDataQuery_keys_all source target parent N P F exponent H Q
        tau a eta kappa delta t _ readMass readInitial readGroup readInteger q readEarlier readCurrent
        oracle predicate hgroup hinteger hearlier hcurrent hmass hinitial

end Keys

end EditApproximation

end OAI
