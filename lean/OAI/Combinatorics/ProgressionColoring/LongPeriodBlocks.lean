import OAI.Combinatorics.ProgressionColoring.AdaptiveMesh
import OAI.Combinatorics.ProgressionColoring.RationalSeparation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Full blocks in the long-period alternative

All displacements are actual real representatives modulo an explicitly
integral error. In particular, the heavy anchor in the stationary-coordinate
argument need not be a regular position.
-/

namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- Re-anchor an actual rational path at the beginning of a full block. -/
theorem rational_full_block_reanchor {k h j₀ : ℕ} {a : ℤ} {y v : ℝ}
    (Y : ℕ → ℝ) (hh : 0 < h) (hfull : j₀ + h ≤ k)
    (hpath : ∀ j, j < k → ∃ e : ℤ,
      Y j - y - (j : ℝ) / h * ((a : ℝ) + v) = e) :
    ∀ z : Fin h, ∃ e : ℤ,
      Y (j₀ + z.val) - Y j₀ - (z.val : ℝ) / h * ((a : ℝ) + v) = e := by
  intro z
  obtain ⟨e₀, he₀⟩ := hpath j₀ (by omega)
  obtain ⟨ez, hez⟩ := hpath (j₀ + z.val) (by omega)
  refine ⟨ez - e₀, ?_⟩
  push_cast at hez ⊢
  calc
    _ = (Y (j₀ + z.val) - y - ((j₀ : ℝ) + z.val) / h * ((a : ℝ) + v)) -
        (Y j₀ - y - (j₀ : ℝ) / h * ((a : ℝ) + v)) := by ring
    _ = _ := by rw [hez, he₀]

/-- A block displacement accumulates at most one unit of its drift vector. -/
theorem full_block_drift_le {h : ℕ} (hh : 0 < h) (z w : Fin h) (v : ℝ) :
    |((z.val : ℝ) - w.val) / h * v| ≤ |v| := by
  have hd := index_drift_le (a := z.val) (b := w.val) (k := h) (h := h)
    (u := v) (U := (h : ℝ) * |v|) z.isLt w.isLt hh le_rfl
  have hhR : (h : ℝ) ≠ 0 := by positivity
  simpa only [mul_div_cancel_left₀ _ hhR] using hd

/-- If the rational step is integral, every pair of block positions is
within one drift amplitude modulo integers, including centered cut crossings. -/
theorem stationary_full_block_distance {h : ℕ} {a : ℤ} {y v : ℝ}
    (Y : Fin h → ℝ) (hh : 0 < h) (hstationary : (h : ℤ) ∣ a)
    (hpath : ∀ z, ∃ e : ℤ,
      Y z - y - (z.val : ℝ) / h * ((a : ℝ) + v) = e)
    (z w : Fin h) :
    ∃ e : ℤ, |centered (Y z) - centered (Y w) - e| ≤ |v| := by
  obtain ⟨c, hc⟩ := hstationary
  obtain ⟨ez, hez⟩ := hpath z
  obtain ⟨ew, hew⟩ := hpath w
  let e : ℤ := ez - ew + ((z.val : ℤ) - w.val) * c -
    ⌊Y z + 1 / 2⌋ + ⌊Y w + 1 / 2⌋
  refine ⟨e, ?_⟩
  have ha : (a : ℝ) = (h : ℝ) * c := by exact_mod_cast hc
  have hhR : (h : ℝ) ≠ 0 := by positivity
  have hquot (u : ℝ) : u / h * (a : ℝ) = u * c := by
    rw [ha]
    field_simp
  have hdiff : centered (Y z) - centered (Y w) - (e : ℝ) =
      ((z.val : ℝ) - w.val) / h * v := by
    dsimp [centered, e]
    push_cast
    have hz : (z.val : ℝ) / h * ((a : ℝ) + v) =
        (z.val : ℝ) * c + (z.val : ℝ) / h * v := by
      rw [mul_add, hquot]
    have hw : (w.val : ℝ) / h * ((a : ℝ) + v) =
        (w.val : ℝ) * c + (w.val : ℝ) / h * v := by
      rw [mul_add, hquot]
    rw [hz] at hez
    rw [hw] at hew
    have hr : ((z.val : ℝ) - w.val) / h * v =
        (z.val : ℝ) / h * v - (w.val : ℝ) / h * v := by ring
    rw [hr]
    nlinarith
  rw [hdiff]
  exact full_block_drift_le hh z w v

/-- Actual stationary-coordinate interval widths satisfy eligibility at
every position, using any heavy anchor, without regularity of that anchor. -/
theorem stationary_full_block_width (A : AdaptiveMesh)
    {h : ℕ} {a : ℤ} {y v : ℝ} (Y : Fin h → ℝ)
    (hh : 0 < h) (hstationary : (h : ℤ) ∣ a)
    (hpath : ∀ z, ∃ e : ℤ,
      Y z - y - (z.val : ℝ) / h * ((a : ℝ) + v) = e)
    (anchor : Fin h)
    (hrelative : |v| ≤ A.width (A.meshLabel (Y anchor)) / 16) :
    ∀ z, |v| ≤ A.width (A.meshLabel (Y z)) := by
  intro z
  have hx := A.meshLabel_contains (Y anchor)
  have hy := A.meshLabel_contains (Y z)
  obtain ⟨e, he⟩ := stationary_full_block_distance Y hh hstationary hpath z anchor
  have hwidthpos := A.width_pos (A.meshLabel (Y anchor))
  have hnear : ∃ e : ℤ, |centered (Y z) - centered (Y anchor) - e| ≤
      2 * A.width (A.meshLabel (Y anchor)) := by
    exact ⟨e, he.trans (by linarith)⟩
  exact hrelative.trans (A.neighbor_width _ _ hx.1 hx.2.le hy.1 hy.2.le hnear)

theorem stationary_relative_width_threshold {M k L v : ℝ}
    (hL : 0 ≤ L) (hsmall : 2 * M / k ≤ 1 / 16)
    (hrelative : |v| ≤ (2 * M / k) * L) : |v| ≤ L / 16 := by
  have h := mul_le_mul_of_nonneg_right hsmall hL
  nlinarith

/-- A truly nonregular sample must be near the cut in its undrifted grid.
The error is explicitly integral; this includes every representative cut. -/
theorem nonregular_implies_grid_near {h : ℕ} (hh : 0 < h)
    (z : Fin h) {a : ℝ} {y v actual η : ℝ}
    (hpath : ∃ e : ℤ,
      actual - y - (z.val : ℝ) / h * (a + v) = e)
    (hdrift : |v| < η) (hbad : rho actual < η) :
    rho (y + (z.val : ℝ) * a / h) < 2 * η := by
  obtain ⟨e, he⟩ := hpath
  have herror : actual - (y + (z.val : ℝ) * a / h) - e =
      (z.val : ℝ) / h * v := by
    calc
      _ = (actual - y - (z.val : ℝ) / h * (a + v) - e) +
          (z.val : ℝ) / h * v := by ring
      _ = _ := by rw [he]; ring
  have hsmall : |(z.val : ℝ) / h * v| ≤ |v| := by
    have hhR : (0 : ℝ) < h := by positivity
    have hz : (z.val : ℝ) ≤ h := by exact_mod_cast z.isLt.le
    have hz0 : (0 : ℝ) ≤ z.val := Nat.cast_nonneg z.val
    rw [abs_mul, abs_of_nonneg (div_nonneg hz0 hhR.le)]
    exact mul_le_of_le_one_left (abs_nonneg v) ((div_le_one hhR).mpr hz)
  have hlip := rho_lipschitz_integer actual (y + (z.val : ℝ) * a / h) e
  rw [herror] at hlip
  have hlow := (abs_le.mp (hlip.trans hsmall)).1
  linarith

end QuantitativeVanDerWaerden

end OAI
