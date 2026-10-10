import Mathlib

namespace OAI

namespace AngularPartitionIdentities

lemma node_zero (m : ℕ) : -1 + 2 * (0 : ℝ) / (m : ℝ) = -1 := by simp

lemma node_last {m : ℕ} (hm : 0 < m) :
    -1 + 2 * (m : ℝ) / (m : ℝ) = 1 := by
  have hn : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma node_step (m j : ℕ) :
    (-1 + 2 * ((j+1 : ℕ) : ℝ) / (m : ℝ)) -
      (-1 + 2 * (j : ℝ) / (m : ℝ)) = 2 / (m : ℝ) := by
  push_cast
  ring

lemma node_strict {m : ℕ} (hm : 0 < m) (j : ℕ) :
    -1 + 2 * (j : ℝ) / (m : ℝ) <
      -1 + 2 * ((j+1 : ℕ) : ℝ) / (m : ℝ) := by
  have hw := node_step m j
  have hp : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  linarith

lemma node_bounds {m : ℕ} (hm : 0 < m) {j : ℕ} (hj : j ≤ m) :
    -1 ≤ -1 + 2 * (j : ℝ) / (m : ℝ) ∧
      -1 + 2 * (j : ℝ) / (m : ℝ) ≤ 1 := by
  have hm' : (0 : ℝ) < m := by positivity
  have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
  have hnonneg : (0 : ℝ) ≤ 2 * (j : ℝ) / (m : ℝ) := by positivity
  have hupper : 2 * (j : ℝ) / (m : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hm').mpr
    linarith
  constructor <;> linarith

lemma node_abs_le {m : ℕ} (hm : 0 < m) {j : ℕ} (hj : j ≤ m) :
    |-1 + 2 * (j : ℝ) / (m : ℝ)| ≤ 1 :=
  abs_le.mpr (node_bounds hm hj)

lemma node_width_le {m : ℕ} {M τ : ℝ}
    (hmesh : 2 / (m : ℝ) ≤ M * τ^2) (j : ℕ) :
    (-1 + 2 * ((j+1 : ℕ) : ℝ) / (m : ℝ)) -
      (-1 + 2 * (j : ℝ) / (m : ℝ)) ≤ M * τ^2 := by
  rw [node_step]
  exact hmesh

theorem partition_properties {m : ℕ} (hm : 0 < m) {M τ : ℝ}
    (hmesh : 2 / (m : ℝ) ≤ M * τ^2) :
    let q : ℕ → ℝ := fun j => -1 + 2 * (j : ℝ) / (m : ℝ)
    q 0 = -1 ∧ q m = 1 ∧
    (∀ j < m, q j < q (j+1)) ∧
    (∀ j ≤ m, |q j| ≤ 1) ∧
    (∀ j < m, q (j+1)-q j ≤ M*τ^2) := by
  exact ⟨by simp, node_last hm, fun j _ => node_strict hm j,
    fun _ hj => node_abs_le hm hj, fun j _ => node_width_le hmesh j⟩

end AngularPartitionIdentities

end OAI
