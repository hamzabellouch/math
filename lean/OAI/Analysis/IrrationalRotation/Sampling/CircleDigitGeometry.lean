import OAI.Analysis.IrrationalRotation.Model.CircleDigitCoupling
import OAI.Analysis.IrrationalRotation.Analysis.UniformQuantization
import Mathlib.Tactic

namespace OAI

noncomputable section
open Set
namespace Invariant233.CircleDigitCoupling

lemma bin_subset_unit {r : ℕ} [NeZero r] (d : Fin r) :
    bin r d ⊆ Ico (0 : ℝ) 1 := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  intro x hx
  have hd : (d : ℝ) + 1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt d.isLt
  exact ⟨(div_nonneg (by positivity) hr.le).trans hx.1,
    hx.2.trans_le ((div_le_iff₀ hr).mpr (by simpa using hd))⟩

lemma bin_length {r : ℕ} (d : Fin r) :
    ((d : ℝ) + 1) / r - (d : ℝ) / r = 1 / r := by ring

lemma bin_subset_top_left {r : ℕ} [NeZero r] (d : Fin r)
    {z u w : ℝ} (hz : z ∈ bin r d) (hzu : z < u) (hu : u ≤ 1 - w)
    (hsmall : 1 / (r : ℝ) < w / 2) :
    bin r d ⊆ Ico (0 : ℝ) (1 - w / 2) := by
  intro x hx
  have hx0 := (bin_subset_unit d hx).1
  have hlen := bin_length d
  exact ⟨hx0, by dsimp [bin] at hz hx; linarith [hz.1, hx.2]⟩

lemma bin_subset_bottom_right {r : ℕ} [NeZero r] (d : Fin r)
    {z u w : ℝ} (hz : z ∈ bin r d) (hzu : u ≤ z) (hu : w ≤ u)
    (hsmall : 1 / (r : ℝ) < w / 2) :
    bin r d ⊆ Ico (w / 2) (1 : ℝ) := by
  intro x hx
  have hx1 := (bin_subset_unit d hx).2
  have hlen := bin_length d
  exact ⟨by dsimp [bin] at hz hx; linarith [hz.2, hx.1], hx1⟩

lemma abs_sub_lt_bin_width {r : ℕ} (d : Fin r) {x y : ℝ}
    (hx : x ∈ bin r d) (hy : y ∈ bin r d) :
    |x - y| < 1 / (r : ℝ) := by
  rw [abs_lt]
  have hlen := bin_length d
  constructor <;> dsimp [bin] at hx hy <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma top_forces_crossing {r : ℕ} {Y y u w : ℝ}
    (hY : 1 - w / 2 ≤ Y) (hround : |y - Y| ≤ 1 / (r : ℝ))
    (hsmall : 1 / (r : ℝ) < w / 2) (hu : u ≤ 1 - w) : u ≤ y := by
  have h := (abs_le.mp hround).1
  linarith

lemma bottom_forces_crossing {r : ℕ} {X x u w : ℝ}
    (hX : X < w / 2) (hround : |x - X| ≤ 1 / (r : ℝ))
    (hsmall : 1 / (r : ℝ) < w / 2) (hu : w ≤ u) : x < u := by
  have h := (abs_le.mp hround).2
  linarith

end Invariant233.CircleDigitCoupling

end

end OAI
