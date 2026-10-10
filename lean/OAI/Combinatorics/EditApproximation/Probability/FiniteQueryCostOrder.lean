import OAI.Combinatorics.EditApproximation.Geometry.GlobalQueryCost

namespace OAI

namespace EditApproximation.FiniteQuery

theorem cost_mono_weights {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (left right : ι → ℕ) (hle : ∀ key, left key ≤ right key) :
    program.cost oracle left ≤ program.cost oracle right := by
  induction program with
  | done result => exact le_rfl
  | read key next ih => exact Nat.add_le_add (hle key) (ih (oracle key))

theorem cost_zero {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι) :
    program.cost oracle (fun _ => 0) = 0 := by
  induction program with
  | done result => rfl
  | read key next ih => simpa only [cost, Nat.zero_add] using ih (oracle key)

theorem cost_eq_zero_of_keys {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (weight : ι → ℕ) (hzero : ∀ key ∈ program.keys oracle, weight key = 0) :
    program.cost oracle weight = 0 :=
  (cost_congr_weights oracle program weight (fun _ => 0) hzero).trans (cost_zero oracle program)

end EditApproximation.FiniteQuery

end OAI
