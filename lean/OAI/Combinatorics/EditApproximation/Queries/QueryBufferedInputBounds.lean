import OAI.Combinatorics.EditApproximation.Binary.BinaryBufferInputBounds
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalBuffers
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryInputs

namespace OAI

/-! Numeric input records for the actual adaptive buffers. Earlier values
are bounded by the separately gathered child-initial table, including at
keys absent from the buffers, where the executable lookup returns zero. -/

namespace EditApproximation.BinaryFraction

theorem queryGatheredRefinementHistory_range {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent t Rp : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (parentInitial : TargetInterval ny → BinaryFraction × ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp) (q : TargetInterval ny)
    (historical : Fin M × ℕ × TargetInterval ny → BinaryFraction)
    (initial : Fin M × TargetInterval ny → BinaryFraction)
    (hnonneg : ∀ input, 0 ≤ (historical input).value)
    (hinitial : ∀ input, 0 ≤ (initial input).value)
    (hbound : ∀ input, (historical input).value ≤ (initial (input.1, input.2.2)).value)
    (s : ℕ) (input : Fin M × TargetInterval ny) :
    let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
    let band := (queryBandInputsWithWork M parent N P F exponent hP a parentInitial q).1
    0 ≤ (queryHistoryReadWithWork earlier (earlier.map historical) s input).1.value ∧
      (queryHistoryReadWithWork earlier (earlier.map historical) s input).1.value ≤
        (queryChildReadWithWork band (band.map initial) input.1 input.2).1.value := by
  have h := gatheredRefinementHistory_range parent N P F exponent t a.value
    (fun r => (parentInitial r).1.value) q queryHistoryEqualWithWork coordinateEqualWithWork
    queryHistoryEqualWithWork_value coordinateEqualWithWork_value historical initial
    hnonneg hinitial hbound (input.1, s, input.2)
  simpa only [queryHistoryReadWithWork, queryChildReadWithWork,
    queryEarlierInputsWithWork_value M parent N P F exponent t hP a parentInitial q Rp hp,
    queryBandInputsWithWork_value M parent N P F exponent hP a parentInitial q Rp hp] using h

theorem queryBufferedRefinementInputBounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent H Q eM eF B E S t Rp : ℕ) (hP : 0 < P)
    (tau a eta kappa delta : BinaryFraction)
    (parentInitial : TargetInterval ny → BinaryFraction × ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp) (q : TargetInterval ny)
    (massWords currentWords : List BinaryFraction) (currentKeys : List (Fin M × TargetInterval ny))
    (historical : Fin M × ℕ × TargetInterval ny → BinaryFraction)
    (initial : Fin M × TargetInterval ny → BinaryFraction)
    (integer : ℕ → TargetInterval ny → ℕ)
    (hn : PreparedKernelNumericBounds (nx := nx) (M := M) N P F exponent H Q eM eF B E S (t - 1)
      tau a eta kappa delta integer)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpn : ∀ r, 0 ≤ (parentInitial r).1.value)
    (hmw : ∀ w ∈ massWords, w.width ≤ B) (hcw : ∀ w ∈ currentWords, w.width ≤ B)
    (hiw : ∀ input, (initial input).width ≤ B) (hhw : ∀ input, (historical input).width ≤ B)
    (hin : ∀ input, 0 ≤ (initial input).value) (hhn : ∀ input, 0 ≤ (historical input).value)
    (hbound : ∀ input, (historical input).value ≤ (initial (input.1, input.2.2)).value) :
    let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
    let band := (queryBandInputsWithWork M parent N P F exponent hP a parentInitial q).1
    PreparedKernelInputBounds (nx := nx) N P F exponent H Q eM eF B E S (t - 1)
      tau a eta kappa delta (fun r => (parentInitial r).1)
      (fun i r => (queryChildReadWithWork band massWords i r).1)
      (fun i r => (queryChildReadWithWork band (band.map initial) i r).1)
      (fun input => (queryHistoryReadWithWork earlier (earlier.map historical) (t - 1) input).1)
      (fun input => (queryChildReadWithWork currentKeys currentWords input.1 input.2).1)
      (fun s input => (queryHistoryReadWithWork earlier (earlier.map historical) s input).1) integer := by
  let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
  let band := (queryBandInputsWithWork M parent N P F exponent hP a parentInitial q).1
  have hB : 2 ≤ B := by have := hn.largeBits; omega
  have hew : ∀ w ∈ earlier.map historical, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hhw key
  have hiw' : ∀ w ∈ band.map initial, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hiw key
  apply hn.with_independent_cached_values
  · exact hpw
  · intro i r
    exact gatheredWordLookupWithWork_width _ band massWords (i, r) B hB hmw
  · intro i r
    exact gatheredWordLookupWithWork_width _ band (band.map initial) (i, r) B hB hiw'
  · intro input
    exact queryHistoryReadWithWork_width earlier (earlier.map historical) (t - 1) input B hB hew
  · intro input
    exact gatheredWordLookupWithWork_width _ currentKeys currentWords input B hB hcw
  · intro s _ i r
    exact queryHistoryReadWithWork_width earlier (earlier.map historical) s (i, r) B hB hew
  · exact hpn
  · intro s _ i r
    exact queryGatheredRefinementHistory_range parent N P F exponent t Rp hP a parentInitial hp q
      historical initial hhn hin hbound s (i, r)

end EditApproximation.BinaryFraction

end OAI
