import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionParameters
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortSubdivision

namespace OAI

/-! Subdivide before applying the major-arc perturbation estimate. The
chosen length keeps the phase variation bounded and still satisfies the
lower length required by the small-divisor correction. -/

namespace TwoPointCorrelations

noncomputable def mrtArcSubdivisionLength (H : ℕ) (W : ℝ) : ℕ := ⌊(H : ℝ) / W⌋₊

lemma mrt_arc_subdivision_bounds {H : ℕ} {W : ℝ}
    (hW : 2 ≤ W) (hH : W ^ (250 : ℕ) ≤ (H : ℝ)) :
    0 < mrtArcSubdivisionLength H W ∧ mrtArcSubdivisionLength H W ≤ H ∧
      (H : ℝ) / W ^ (2 : ℕ) ≤ (mrtArcSubdivisionLength H W : ℝ) ∧
      (mrtArcSubdivisionLength H W : ℝ) ≤ (H : ℝ) / W := by
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hH0 : (0 : ℝ) < H := (pow_pos hW0 250).trans_le hH
  have hp : W ^ (2 : ℕ) ≤ (H : ℝ) :=
    (pow_le_pow_right₀ hW1 (by norm_num : (2 : ℕ) ≤ 250)).trans hH
  have hWsq : 2 * W ≤ W ^ (2 : ℕ) := by nlinarith
  have htwo : (2 : ℝ) ≤ (H : ℝ) / W :=
    (le_div_iff₀ hW0).mpr (hWsq.trans hp)
  have hfloor := Nat.lt_floor_add_one ((H : ℝ) / W)
  have hlow : ((H : ℝ) / W) / 2 ≤ (mrtArcSubdivisionLength H W : ℝ) := by
    change (H : ℝ) / W / 2 ≤ (⌊(H : ℝ) / W⌋₊ : ℝ)
    linarith
  have hupper : (mrtArcSubdivisionLength H W : ℝ) ≤ (H : ℝ) / W :=
    Nat.floor_le (div_nonneg hH0.le hW0.le)
  refine ⟨Nat.floor_pos.mpr (by linarith), ?_, ?_, hupper⟩
  · have hh := hupper.trans (div_le_self hH0.le hW1)
    exact_mod_cast hh
  · calc
      _ ≤ (H : ℝ) / (2 * W) :=
        div_le_div_of_nonneg_left hH0.le (by positivity) hWsq
      _ = ((H : ℝ) / W) / 2 := by ring
      _ ≤ _ := hlow

lemma mrt_arc_subdivision_remainder {H : ℕ} {W : ℝ}
    (hW : 2 ≤ W) (hH : W ^ (250 : ℕ) ≤ (H : ℝ)) :
    (mrtArcSubdivisionLength H W : ℝ) / H ≤ W ^ (-(1 / 4 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have hH0 : (0 : ℝ) < H := (pow_pos hW0 250).trans_le hH
  have hupper := (mrt_arc_subdivision_bounds hW hH).2.2.2
  calc
    _ ≤ ((H : ℝ) / W) / H := div_le_div_of_nonneg_right hupper hH0.le
    _ = W ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; field_simp
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)

lemma mrt_arc_subdivision_phase {H q : ℕ} {W β : ℝ}
    (hW : 2 ≤ W) (hH : W ^ (250 : ℕ) ≤ (H : ℝ)) (hq : 0 < q)
    (hβ : |β| ≤ W / ((H : ℝ) * q)) :
    |β| * (mrtArcSubdivisionLength H W : ℝ) ≤ 1 / (q : ℝ) := by
  have hW0 : 0 < W := by linarith
  have hH0 : (0 : ℝ) < H := (pow_pos hW0 250).trans_le hH
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hh := (mrt_arc_subdivision_bounds hW hH).2.2.2
  calc
    _ ≤ (W / ((H : ℝ) * q)) * ((H : ℝ) / W) :=
      mul_le_mul hβ hh (Nat.cast_nonneg _) (by positivity)
    _ = _ := by field_simp

theorem mrt_arc_subdivision_integral (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) (hHX : H ≤ X) {W ε : ℝ}
    (hW : 2 ≤ W) (hH : W ^ (250 : ℕ) ≤ (H : ℝ)) (hε : 0 ≤ ε) (α : ℝ)
    (hshort : shortExponentialIntegral F (X + H) (mrtArcSubdivisionLength H W) α ≤
      ε * (X + H : ℕ) * (mrtArcSubdivisionLength H W : ℝ)) :
    shortExponentialIntegral F X H α ≤
      (X : ℝ) * H * (2 * ε + W ^ (-(1 / 4 : ℝ))) := by
  let h := mrtArcSubdivisionLength H W
  have hh : 0 < h := (mrt_arc_subdivision_bounds hW hH).1
  have hH0 : (0 : ℝ) < H := (pow_pos (by linarith : 0 < W) 250).trans_le hH
  have hcount : (H / h : ℕ) * (h : ℝ) ≤ H := by
    exact_mod_cast Nat.div_mul_le_self H h
  have hX : (X + H : ℕ) ≤ (2 : ℝ) * X := by
    have hreal : (H : ℝ) ≤ X := by exact_mod_cast hHX
    push_cast
    linarith
  have hmain : (H / h : ℕ) * shortExponentialIntegral F (X + H) h α ≤
      2 * ε * X * H := by
    calc
      _ ≤ (H / h : ℕ) * (ε * (X + H : ℕ) * (h : ℝ)) :=
        mul_le_mul_of_nonneg_left hshort (Nat.cast_nonneg _)
      _ = (ε * (X + H : ℕ)) * ((H / h : ℕ) * (h : ℝ)) := by ring
      _ ≤ (ε * ((2 : ℝ) * X)) * (H : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hX hε) hcount
          (by positivity) (by positivity)
      _ = _ := by ring
  have hrem : (X : ℝ) * h ≤ (X : ℝ) * H * W ^ (-(1 / 4 : ℝ)) := by
    have hb := (div_le_iff₀ hH0).mp (mrt_arc_subdivision_remainder hW hH)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg X)
  calc
    _ ≤ (H / h : ℕ) * shortExponentialIntegral F (X + H) h α + (X : ℝ) * h :=
      mrt_short_integral_subdivision F hF X H h hh α
    _ ≤ 2 * ε * X * H + (X : ℝ) * H * W ^ (-(1 / 4 : ℝ)) := add_le_add hmain hrem
    _ = _ := by ring

end TwoPointCorrelations

end OAI
