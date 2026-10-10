import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Finite scalar bins

A bounded interval is covered by explicitly indexed half-open intervals of
length `η`. The extra final bin includes the top endpoint even when `U / η`
is an integer.
-/

namespace Tingley

/-- Cover `[0,U]` by finitely many scalar bins with pairwise distance at most
`η` inside each bin. The construction also works when `U = 0`. -/
theorem exists_finite_scalar_bins {U η : ℝ} (_hU : 0 ≤ U) (hη : 0 < η) :
    ∃ N : ℕ, ∃ B : Fin N → Set ℝ,
      Set.Icc 0 U ⊆ ⋃ k, B k ∧
      ∀ k, ∀ x ∈ B k, ∀ y ∈ B k, |x - y| ≤ η := by
  let N : ℕ := Nat.floor (U / η) + 1
  let B : Fin N → Set ℝ := fun k =>
    Set.Ico ((k.val : ℝ) * η) (((k.val : ℝ) + 1) * η)
  refine ⟨N, B, ?_, ?_⟩
  · intro x hx
    have hkU : Nat.floor (x / η) ≤ Nat.floor (U / η) :=
      Nat.floor_mono (div_le_div_of_nonneg_right hx.2 hη.le)
    have hkN : Nat.floor (x / η) < N := Nat.lt_succ_of_le hkU
    refine Set.mem_iUnion.mpr ⟨⟨Nat.floor (x / η), hkN⟩, ?_⟩
    change (Nat.floor (x / η) : ℝ) * η ≤ x ∧
      x < ((Nat.floor (x / η) : ℝ) + 1) * η
    exact ⟨(le_div_iff₀ hη).mp (Nat.floor_le (div_nonneg hx.1 hη.le)),
      (div_lt_iff₀ hη).mp (Nat.lt_floor_add_one (x / η))⟩
  · intro k x hx y hy
    change (k.val : ℝ) * η ≤ x ∧ x < ((k.val : ℝ) + 1) * η at hx
    change (k.val : ℝ) * η ≤ y ∧ y < ((k.val : ℝ) + 1) * η at hy
    rw [add_mul, one_mul] at hx hy
    apply abs_le.mpr
    constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]

end Tingley

end OAI
