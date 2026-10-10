import Mathlib

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def midpoint (p : ℕ) (i : Fin p) : ℝ := -1 + (2*(i:ℝ)+1)/p

noncomputable def index (p : ℕ) (hp : 0 < p) (x : ℝ) : Fin p :=
  ⟨min ⌊(p:ℝ)*(x+1)/2⌋₊ (p-1), (min_le_right _ _).trans_lt (by omega)⟩

theorem index_measurable (p : ℕ) (hp : 0 < p) : Measurable (index p hp) := by
  let g : ℕ → Fin p := fun k => ⟨min k (p-1), (min_le_right _ _).trans_lt (by omega)⟩
  exact (measurable_of_countable g).comp
    (((measurable_const.mul (measurable_id.add_const 1)).div_const 2).nat_floor)

theorem floor_lt_on_interval (p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) : ⌊(p:ℝ)*(x+1)/2⌋₊ < p := by
  apply (Nat.floor_lt' (Nat.ne_of_gt hp)).mpr
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  nlinarith [mul_lt_mul_of_pos_left hx.2 hpR]

theorem index_val_on_interval (p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) : (index p hp x).val = ⌊(p:ℝ)*(x+1)/2⌋₊ := by
  exact min_eq_left (by have h := floor_lt_on_interval p hp hx; omega)

theorem index_eq_iff_on_interval (p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) (i : Fin p) :
    index p hp x = i ↔ -1 + 2*(i:ℝ)/p ≤ x ∧ x < -1 + 2*((i:ℝ)+1)/p := by
  have hz : 0 ≤ (p:ℝ)*(x+1)/2 := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith [hx.1])) (by norm_num)
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  rw [Fin.ext_iff, index_val_on_interval p hp hx, Nat.floor_eq_iff hz]
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · have h : 2*(i:ℝ)/p ≤ x+1 := (div_le_iff₀ hpR).mpr (by nlinarith)
      linarith
    · have h : x+1 < 2*((i:ℝ)+1)/p := (lt_div_iff₀ hpR).mpr (by nlinarith)
      linarith
  · rintro ⟨hl, hu⟩
    have hL : 2*(i:ℝ) ≤ (x+1)*p := (div_le_iff₀ hpR).mp (by linarith)
    have hU : (x+1)*p < 2*((i:ℝ)+1) := (lt_div_iff₀ hpR).mp (by linarith)
    constructor <;> nlinarith

end VertexCover.GridCoupling
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem cell_subset_interval (p : ℕ) (hp : 0 < p) (i : Fin p) :
    Set.Ico (-1 + 2*(i:ℝ)/p) (-1 + 2*((i:ℝ)+1)/p) ⊆ Set.Ico (-1:ℝ) 1 := by
  intro x hx
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hi : (i:ℝ)+1 ≤ p := by exact_mod_cast i.isLt
  have hz : 0 ≤ 2*(i:ℝ)/p := div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hpR.le
  have hu : 2*((i:ℝ)+1)/p ≤ 2 := (div_le_iff₀ hpR).mpr (by nlinarith)
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem preimage_cell (p : ℕ) (hp : 0 < p) (i : Fin p) :
    (index p hp ⁻¹' {i}) ∩ Set.Ico (-1:ℝ) 1 =
      Set.Ico (-1 + 2*(i:ℝ)/p) (-1 + 2*((i:ℝ)+1)/p) := by
  ext x
  constructor
  · rintro ⟨hi, hx⟩
    exact (index_eq_iff_on_interval p hp hx i).mp hi
  · intro hx
    have hx' := cell_subset_interval p hp i hx
    exact ⟨(index_eq_iff_on_interval p hp hx' i).mpr hx, hx'⟩

theorem rounding_error (p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) : |x - midpoint p (index p hp x)| ≤ 1/p := by
  have h := (index_eq_iff_on_interval p hp hx (index p hp x)).mp rfl
  unfold midpoint
  rw [abs_le]
  simp only [mul_add, mul_one, add_div] at h ⊢
  have he : (2:ℝ)/p = 2*(1/p) := by ring
  rw [he] at h
  constructor <;> linarith

end VertexCover.GridCoupling

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
