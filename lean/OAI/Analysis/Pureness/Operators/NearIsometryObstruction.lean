import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

namespace OAI
noncomputable section
namespace CuntzPureness
variable {B : Type*} [CStarAlgebra B]

lemma isUnit_of_norm_sub_one_lt (x : B) (hx : ‖x - 1‖ < 1) : IsUnit x := by
  have hh : ‖1 - x‖ < 1 := by simpa only [norm_sub_rev] using hx
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hh

variable [Nontrivial B]

lemma unit_inverse_norm_le_two (q : Bˣ) (hq : ‖(q : B) - 1‖ ≤ 1 / 2) :
    ‖(↑q⁻¹ : B)‖ ≤ 2 := by
  have he : (↑q⁻¹ : B) = 1 - (↑q⁻¹ : B) * ((q : B) - 1) := by
    simp [mul_sub]
  have hn : ‖(↑q⁻¹ : B)‖ ≤ 1 + ‖(↑q⁻¹ : B)‖ * (1 / 2) := by
    calc
      _ = ‖1 - (↑q⁻¹ : B) * ((q : B) - 1)‖ := congrArg norm he
      _ ≤ ‖(1 : B)‖ + ‖(↑q⁻¹ : B) * ((q : B) - 1)‖ := norm_sub_le _ _
      _ ≤ 1 + ‖(↑q⁻¹ : B)‖ * (1 / 2) := by
        rw [norm_one]
        exact add_le_add_right ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left hq (norm_nonneg _))) 1
  linarith

theorem small_perturbation_near_isometry (v w : B)
    (hv : ‖star v * v - 1‖ ≤ 1 / 16) (hvn : ‖v‖ ≤ 1)
    (hwn : ‖w‖ ≤ 1 / 4) (hvu : ¬ IsUnit v) :
    IsUnit (star (v + w) * (v + w)) ∧ ¬ IsUnit (v + w) := by
  have hsq : ‖star (v + w) * (v + w) - 1‖ < 1 := by
    have he : star (v + w) * (v + w) - 1 =
        ((star v * v - 1) + star v * w) + star w * v + star w * w := by
      simp only [star_add]
      noncomm_ring
    have h₁ : ‖star v * w‖ ≤ 1 / 4 := by
      apply (norm_mul_le _ _).trans
      rw [norm_star]
      nlinarith [norm_nonneg v, norm_nonneg w]
    have h₂ : ‖star w * v‖ ≤ 1 / 4 := by
      apply (norm_mul_le _ _).trans
      rw [norm_star]
      nlinarith [norm_nonneg v, norm_nonneg w]
    have h₃ : ‖star w * w‖ ≤ 1 / 16 := by
      rw [CStarRing.norm_star_mul_self]
      nlinarith [norm_nonneg w]
    rw [he]
    have ha := norm_add_le (star v * v - 1) (star v * w)
    have hb := norm_add_le ((star v * v - 1) + star v * w) (star w * v)
    have hc := norm_add_le (((star v * v - 1) + star v * w) + star w * v) (star w * w)
    linarith
  refine ⟨isUnit_of_norm_sub_one_lt _ hsq, ?_⟩
  obtain ⟨q, hq⟩ := isUnit_of_norm_sub_one_lt (star v * v) (hv.trans_lt (by norm_num))
  have hqi : ‖(↑q⁻¹ : B)‖ ≤ 2 := unit_inverse_norm_le_two q (by rw [hq]; linarith)
  let L := (↑q⁻¹ : B) * star v
  have hLv : L * v = 1 := by
    dsimp [L]
    rw [mul_assoc, ← hq]
    simp
  have hL : ‖L‖ ≤ 2 := by
    apply (norm_mul_le _ _).trans
    rw [norm_star]
    nlinarith [norm_nonneg (↑q⁻¹ : B), norm_nonneg v]
  have hwL : ‖w * L‖ < 1 := by
    have hh := norm_mul_le w L
    nlinarith [norm_nonneg w, norm_nonneg L]
  have hunit : IsUnit (1 + w * L) := by
    apply isUnit_of_norm_sub_one_lt
    simpa using hwL
  have he : v + w = (1 + w * L) * v := by
    rw [add_mul, one_mul, mul_assoc, hLv, mul_one]
  intro hy
  rw [he] at hy
  obtain ⟨t, ht⟩ := hunit
  rw [← ht] at hy
  exact hvu ((t.isUnit_units_mul v).mp hy)
end CuntzPureness

end

end OAI
