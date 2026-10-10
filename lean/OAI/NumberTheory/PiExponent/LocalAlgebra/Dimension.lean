import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.PiExponent.Analysis.DimensionLimits

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace PiExponent

def dimensionK (C : ℝ) (m : ℕ) : ℕ := ⌊C ^ m⌋₊

def dimensionW (B : ℝ) (m : ℕ) : ℝ := (B ^ m)⁻¹

def dimensionV (theta B C : ℝ) (m : ℕ) : ℝ :=
  2 * (dimensionK C m : ℝ) * theta ^ m * dimensionW B m

theorem dimensionK_le (C : ℝ) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) ≤ C ^ m :=
  Nat.floor_le (pow_nonneg hC m)

theorem dimensionK_one_le (C : ℝ) (hC : 1 ≤ C) (m : ℕ) :
    1 ≤ dimensionK C m := by
  exact (Nat.one_le_floor_iff _).2 (one_le_pow₀ hC)

theorem dimensionW_pos (B : ℝ) (hB : 0 < B) (m : ℕ) :
    0 < dimensionW B m := by
  exact inv_pos.mpr (pow_pos hB m)

theorem dimensionV_pos (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    0 < dimensionV theta B C m := by
  have hK : 0 < (dimensionK C m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m))
  exact mul_pos (mul_pos (mul_pos (by norm_num) hK) (pow_pos htheta m))
    (dimensionW_pos B hB m)

theorem dimension_volume (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) * (dimensionW B m / dimensionV theta B C m) *
      theta ^ m = 1 / 2 := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hw : dimensionW B m ≠ 0 := ne_of_gt (dimensionW_pos B hB m)
  unfold dimensionV
  field_simp

theorem dimensionK_div_W_le (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) / dimensionW B m ≤ (C * B) ^ m := by
  rw [dimensionW, div_inv_eq_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos hB m).le

theorem dimensionV_geometric_lower (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (C * theta / B) ^ m ≤ dimensionV theta B C m := by
  have hfloor : C ^ m < (dimensionK C m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK : C ^ m ≤ 2 * (dimensionK C m : ℝ) := by linarith
  rw [div_pow, mul_pow, div_eq_mul_inv]
  unfold dimensionV dimensionW
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (pow_pos htheta m).le)
    (inv_pos.mpr (pow_pos hB m)).le

theorem dimension_volume_lt_one (theta C : ℝ) (htheta : 0 < theta)
    (hC : 0 ≤ C) (hsmall : C * theta < 1) (m : ℕ) (hm : 1 ≤ m) :
    (dimensionK C m : ℝ) * theta ^ m < 1 := by
  calc
    (dimensionK C m : ℝ) * theta ^ m ≤ C ^ m * theta ^ m :=
      mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos htheta m).le
    _ = (C * theta) ^ m := (mul_pow _ _ _).symm
    _ < 1 := pow_lt_one₀ (mul_nonneg hC htheta.le) hsmall (by omega)

theorem dimension_error_le (theta B C a b : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m ≤
      (a * (m : ℝ) + b) / (C * theta / B) ^ m + 100 * (C * B) ^ m := by
  have hr : 0 < (C * theta / B) ^ m := by
    have hCp : 0 < C := by
      by_contra hn
      have hz : C = 0 := le_antisymm (le_of_not_gt hn) hC
      subst C
      rcases m with _ | m <;> norm_num at hlarge
    positivity
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hr
      (dimensionV_geometric_lower theta B C htheta hB m hlarge)
  · rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (dimensionK_div_W_le B C hB hC m) (by norm_num)

theorem dimension_collision_identity (theta A B C eta : ℝ)
    (htheta : 0 < theta) (hA : 0 < A) (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    eta ^ 2 * (dimensionK C m : ℝ) * theta ^ m /
        (((m : ℝ) + 1) * dimensionV theta B C m * A ^ m) =
      eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hA' : A ^ m ≠ 0 := ne_of_gt (pow_pos hA m)
  have hB' : B ^ m ≠ 0 := ne_of_gt (pow_pos hB m)
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold dimensionV dimensionW
  rw [div_pow]
  field_simp

theorem tendsto_dimension_error_majorant (theta B C a b : ℝ)
    (hB : 0 < B) (hC : 0 < C) (hsmall : C * B < 1)
    (hlarge : 1 < C * theta / B) :
    Tendsto (fun m : ℕ => (a * (m : ℝ) + b) / (C * theta / B) ^ m +
      100 * (C * B) ^ m) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hlarge
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hlarge
  have hlin : Tendsto (fun m : ℕ => (a * (m : ℝ) + b) /
      (C * theta / B) ^ m) atTop (𝓝 0) := by
    convert (h₁.const_mul a).add (h₀.const_mul b) using 1
    · ext m
      simp only [pow_one, pow_zero]
      ring
    · simp
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hC hB).le hsmall
  simpa only [mul_zero, add_zero] using hlin.add (hgeom.const_mul 100)

theorem tendsto_dimension_collision (A B eta : ℝ)
    (hratio : 1 < B / A) (heta : 0 < eta) :
    Tendsto (fun m : ℕ => eta ^ 2 * (B / A) ^ m /
      (2 * ((m : ℝ) + 1))) atTop atTop := by
  have h := (tendsto_pow_div_nat_add_one hratio).const_mul_atTop
    (show 0 < eta ^ 2 / 2 by positivity)
  convert h using 1
  ext m
  rw [mul_div_mul_comm]

theorem exists_dimension_margin (theta A B C eta a b epsilon target : ℝ)
    (htheta : 0 < theta) (hB : 0 < B) (hC : 1 < C)
    (hsmall : C * B < 1) (hlarge : 1 < C * theta / B)
    (hratio : 1 < B / A) (heta : 0 < eta)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have herrors := (tendsto_dimension_error_majorant theta B C a b hB
    (zero_lt_one.trans hC) hsmall hlarge).eventually (gt_mem_nhds hepsilon)
  have hcollision := (tendsto_dimension_collision A B eta hratio heta).eventually
    (eventually_gt_atTop target)
  have hfloor := (tendsto_pow_atTop_atTop_of_one_lt hC).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hgood : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
    filter_upwards [herrors, hcollision, hfloor, eventually_ge_atTop 1]
      with m herror hcollision hfloor hm
    exact ⟨hm, (dimension_error_le theta B C a b htheta hB
      (zero_lt_one.trans hC).le ha hb m hfloor).trans_lt herror, hcollision⟩
  exact hgood.exists

end PiExponent

end

end OAI
