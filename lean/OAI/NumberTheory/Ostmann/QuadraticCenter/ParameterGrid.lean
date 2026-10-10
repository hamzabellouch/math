import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def parameterGrid (lo hi m : ℕ) : Finset ℝ :=
  (Finset.Icc (lo * m) (hi * m)).image (fun j : ℕ => (j : ℝ) / m)

theorem parameterGrid_card_le (lo hi m : ℕ) :
    (parameterGrid lo hi m).card ≤ hi * m + 1 := by
  apply Finset.card_image_le.trans
  simp only [Nat.card_Icc]
  omega

theorem mem_parameterGrid_bounds {lo hi m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : x ∈ parameterGrid lo hi m) : (lo : ℝ) ≤ x ∧ x ≤ hi := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hl, hh⟩ := Finset.mem_Icc.mp hj
  constructor
  · apply (le_div_iff₀ hmR).mpr
    exact_mod_cast hl
  · apply (div_le_iff₀ hmR).mpr
    exact_mod_cast hh

theorem exists_near_parameterGrid {lo hi m : ℕ} (hm : 0 < m) {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) :
    ∃ x₀ ∈ parameterGrid lo hi m, |x - x₀| ≤ 1 / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 ≤ x := (Nat.cast_nonneg lo).trans hlo
  let j := ⌊x * (m : ℝ)⌋₊
  have hjlo : lo * m ≤ j := Nat.le_floor (by exact_mod_cast (mul_le_mul_of_nonneg_right hlo hmR.le))
  have hjhi : j ≤ hi * m := Nat.floor_le_of_le (by exact_mod_cast (mul_le_mul_of_nonneg_right hhi hmR.le))
  refine ⟨(j : ℝ) / m, Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hjlo, hjhi⟩, rfl⟩, ?_⟩
  have hjle : (j : ℝ) ≤ x * m := Nat.floor_le (mul_nonneg hx0 hmR.le)
  have hjlt : x * m < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [abs_of_nonneg (by apply sub_nonneg.mpr; exact (div_le_iff₀ hmR).mpr hjle)]
  apply (le_div_iff₀ hmR).mpr
  have he : (x - (j : ℝ) / m) * m = x * m - j := by field_simp
  rw [he]
  linarith

theorem exists_near_parameter_pair {B m : ℕ} (hm : 0 < m) {θ R : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hR1 : 1 ≤ R) (hRB : R ≤ B) :
    ∃ z ∈ (parameterGrid 0 1 m).product (parameterGrid 1 B m),
      |θ - z.1| ≤ 1 / (m : ℝ) ∧ |R - z.2| ≤ 1 / (m : ℝ) ∧ 1 ≤ z.2 := by
  obtain ⟨θ₀, hθ₀, hθdist⟩ := exists_near_parameterGrid (lo := 0) (hi := 1) (x := θ) hm (by simpa using hθ0) (by simpa using hθ1)
  obtain ⟨R₀, hR₀, hRdist⟩ := exists_near_parameterGrid (lo := 1) (hi := B) (x := R) hm (by simpa using hR1) hRB
  exact ⟨(θ₀, R₀), Finset.mem_product.mpr ⟨hθ₀, hR₀⟩, hθdist, hRdist,
    by simpa using (mem_parameterGrid_bounds hm hR₀).1⟩

theorem parameter_pair_card_le (B m : ℕ) :
    ((parameterGrid 0 1 m).product (parameterGrid 1 B m)).card ≤ (m + 1) * (B * m + 1) := by
  have hcard : ((parameterGrid 0 1 m).product (parameterGrid 1 B m)).card =
      (parameterGrid 0 1 m).card * (parameterGrid 1 B m).card := Multiset.card_product _ _
  rw [hcard]
  have h1 : (parameterGrid 0 1 m).card ≤ m + 1 := by simpa using parameterGrid_card_le 0 1 m
  exact Nat.mul_le_mul h1 (parameterGrid_card_le 1 B m)

end Ostmann.QuadraticCenter

end

end OAI
