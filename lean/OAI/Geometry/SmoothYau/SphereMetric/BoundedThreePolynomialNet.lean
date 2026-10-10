import Mathlib
import OAI.Geometry.SmoothYau.Estimates.GridPoint

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
namespace YauCounterexamples

theorem bounded_three_polynomial_net (B : ℝ) (hB : 0 < B)
    (c : ℝ) (hc : 0 < c) :
    ∃ C > 0, ∀ K : Set (Fin 3 → ℝ), (∀ x ∈ K, ‖x‖ ≤ B) →
      ∀ n : ℝ, 1 ≤ n → ∃ t : Finset (Fin 3 → ℝ),
      (↑t : Set (Fin 3 → ℝ)) ⊆ K ∧ (t.card : ℝ) ≤ C*n^3 ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ c/n := by
  let A := 4*B/c+3
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A^3,pow_pos hA _,?_⟩
  intro K hbound n hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  let δ := c/(2*n)
  have hδ : 0 < δ := div_pos hc (mul_pos (by norm_num) hn0)
  let m := ⌈B/δ⌉₊
  have hm : B ≤ (m : ℝ)*δ := (div_le_iff₀ hδ).mp (Nat.le_ceil (B/δ))
  obtain ⟨t,htK,htcard,htcover⟩ := cube_subset_finite_net 3 m δ hδ K
    (fun x hx => (hbound x hx).trans hm)
  refine ⟨t,htK,?_,?_⟩
  · have hm' : (m : ℝ) < B/δ+1 := Nat.ceil_lt_add_one (div_nonneg hB.le hδ.le)
    have heq : B/δ = (2*B/c)*n := by dsimp [δ]; field_simp
    have hbase : (2*m+1 : ℝ) ≤ A*n := by
      dsimp [A]
      rw [heq] at hm'
      have hid : (4*B/c+3)*n = 2*((2*B/c)*n)+3*n := by ring
      rw [hid]
      linarith
    calc
      (t.card : ℝ) ≤ ((2*m+1)^3 : ℕ) := by exact_mod_cast htcard
      _ = (2*(m : ℝ)+1)^3 := by norm_cast
      _ ≤ (A*n)^3 := pow_le_pow_left₀ (by positivity) hbase _
      _ = A^3*n^3 := mul_pow _ _ _
  · intro x hx
    obtain ⟨y,hy,hd⟩ := htcover x hx
    refine ⟨y,hy,?_⟩
    convert hd using 1
    dsimp [δ]
    field_simp

end YauCounterexamples

end

end OAI
