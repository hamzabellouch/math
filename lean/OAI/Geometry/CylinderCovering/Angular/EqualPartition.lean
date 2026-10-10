import Mathlib

namespace OAI

namespace CylinderCovering.AngularEqualPartition

lemma left_endpoint (m : ℕ) : (-1 : ℝ) + 2 * (0 : ℕ) / m = -1 := by
  simp

lemma right_endpoint {m : ℕ} (hm : 0 < m) :
    (-1 : ℝ) + 2 * (m : ℝ) / m = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma width (m j : ℕ) :
    ((-1 : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) / m) -
      ((-1 : ℝ) + 2 * (j : ℝ) / m) = 2 / m := by
  push_cast
  ring

lemma strictly_increasing {m : ℕ} (hm : 0 < m) (j : ℕ) :
    ((-1 : ℝ) + 2 * (j : ℝ) / m) <
      ((-1 : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) / m) := by
  have hw := width m j
  have hp : (0 : ℝ) < 2 / m := by positivity
  linarith only [hw, hp]

lemma absolute_bound {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    |(-1 : ℝ) + 2 * (j : ℝ) / m| ≤ 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjR : (j : ℝ) ≤ m := by exact_mod_cast hj
  have hl : (0 : ℝ) ≤ 2 * (j : ℝ) / m := by positivity
  have hu : 2 * (j : ℝ) / m ≤ 2 := by
    apply (div_le_iff₀ hmR).2
    linarith only [hjR]
  exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hu]⟩

theorem partition_laws {m : ℕ} {M τ : ℝ} (hm : 0 < m)
    (hmesh : (2 : ℝ) / m ≤ M * τ ^ 2) :
    (fun j : ℕ => (-1 : ℝ) + 2 * (j : ℝ) / m) 0 = -1 ∧
    (fun j : ℕ => (-1 : ℝ) + 2 * (j : ℝ) / m) m = 1 ∧
    (∀ j < m, (-1 : ℝ) + 2 * (j : ℝ) / m <
      (-1 : ℝ) + 2 * ((j+1 : ℕ) : ℝ) / m) ∧
    (∀ j ≤ m, |(-1 : ℝ) + 2 * (j : ℝ) / m| ≤ 1) ∧
    ∀ j < m, ((-1 : ℝ) + 2 * ((j+1 : ℕ) : ℝ) / m) -
      ((-1 : ℝ) + 2 * (j : ℝ) / m) ≤ M * τ ^ 2 := by
  refine ⟨left_endpoint m, right_endpoint hm,
    fun j _ => strictly_increasing hm j, fun j hj => absolute_bound hm hj, ?_⟩
  intro j _
  rw [width]
  exact hmesh

end CylinderCovering.AngularEqualPartition

end OAI
