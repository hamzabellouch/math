import OAI.NumberTheory.EgyptianFractions.BackwardExpansions

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.Descent

/-- Convert an ordinary positive list to the finite-tuple interface used by
backward propagation, without changing its length or reciprocal sum. -/
theorem UnitListAtMost.of_list {x : ℚ} {B : ℕ} (l : List ℕ)
    (hlen : l.length ≤ B) (hpos : ∀ n ∈ l, 0 < n)
    (hsum : (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = x) :
    UnitListAtMost x B := by
  refine ⟨l.length, hlen, l.get, fun i => hpos _ (l.get_mem i), ?_⟩
  calc
    (∑ i : Fin l.length, (1 : ℚ) / (l.get i : ℚ)) =
        (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum := by
      rw [← List.sum_ofFn]
      change (List.ofFn ((fun n : ℕ => (1 : ℚ) / (n : ℚ)) ∘ l.get)).sum = _
      rw [← List.map_ofFn, List.ofFn_get]
    _ = x := hsum

/-- A real-valued length budget can be rounded once at the terminal stage. -/
theorem UnitListAtMost.of_list_real {x : ℚ} {L : ℝ} (l : List ℕ)
    (hlen : (l.length : ℝ) ≤ L) (hpos : ∀ n ∈ l, 0 < n)
    (hsum : (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = x) :
    UnitListAtMost x ⌈L⌉₊ := by
  apply UnitListAtMost.of_list l _ hpos hsum
  exact_mod_cast hlen.trans (Nat.le_ceil L)

/-- Convert the propagated finite tuple back to the list interface in the
dense-family proposition. -/
theorem UnitListAtMost.to_list {x : ℚ} {B : ℕ} (H : UnitListAtMost x B) :
    ∃ l : List ℕ, l.length ≤ B ∧ (∀ n ∈ l, 0 < n) ∧
      (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = x := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H
  refine ⟨List.ofFn n, by simpa using hk, ?_, ?_⟩
  · intro d hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
    exact hn i
  · simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hsum

/-- Below one the output additionally meets the required denominator-two bound. -/
theorem UnitListAtMost.to_list_two {x : ℚ} {B : ℕ} (H : UnitListAtMost x B)
    (hx : x < 1) :
    ∃ l : List ℕ, l.length ≤ B ∧ (∀ n ∈ l, 2 ≤ n) ∧
      (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = x := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H.denominators_two hx
  refine ⟨List.ofFn n, by simpa using hk, ?_, ?_⟩
  · intro d hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
    exact hn i
  · simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hsum

end Problem337.Descent

end

end OAI
