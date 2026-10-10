import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose

namespace OAI

/-!
# Affinity of representatives inside a small box

The input is the integer-valued cross difference of three representatives of
an arithmetic progression modulo one. A box of width `2 * H` makes this integer
strictly smaller than one in absolute value, so it vanishes. Interpolation then
produces one real affine lift on all selected indices.
-/

universe uIndex

namespace QuantitativeVanDerWaerden

/-- An integer whose real absolute value is less than one vanishes. -/
theorem integer_zero_of_abs_lt_one {m : ℤ} (h : |(m : ℝ)| < 1) : m = 0 := by
  have hm : |m| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp hm

/-- Integer errors in affine representatives imply an integer cross difference.
No ordering assumption on the three indices is needed here. -/
theorem triple_integral_of_integer_errors {z : ℕ → ℝ} {A B : ℝ}
    (h : ∀ j, ∃ m : ℤ, z j - A - (j : ℝ) * B = (m : ℝ))
    (a b c : ℕ) :
    ∃ m : ℤ, ((c : ℝ) - b) * (z b - z a) -
      ((b : ℝ) - a) * (z c - z b) = (m : ℝ) := by
  obtain ⟨ma, ha⟩ := h a
  obtain ⟨mb, hb⟩ := h b
  obtain ⟨mc, hc⟩ := h c
  have hza : z a = A + (a : ℝ) * B + (ma : ℝ) := by linarith
  have hzb : z b = A + (b : ℝ) * B + (mb : ℝ) := by linarith
  have hzc : z c = A + (c : ℝ) * B + (mc : ℝ) := by linarith
  refine ⟨((c : ℤ) - b) * (mb - ma) - ((b : ℤ) - a) * (mc - mb), ?_⟩
  rw [hza, hzb, hzc]
  push_cast
  ring

/-- The cross difference of three points in a short real interval is small. -/
theorem abs_cross_difference_lt_one {k a b c : ℕ} {H : ℝ} {z : ℕ → ℝ}
    (hab : a < b) (hbc : b < c) (hck : c < k)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (habox : |z b - z a| ≤ 2 * H) (hbbox : |z c - z b| ≤ 2 * H) :
    |((c : ℝ) - b) * (z b - z a) -
      ((b : ℝ) - a) * (z c - z b)| < 1 := by
  have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc.le
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hp : 0 ≤ (c : ℝ) - b := sub_nonneg.mpr hbc'
  have hq : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr hab'
  have hck' : (c : ℝ) ≤ k := by exact_mod_cast hck.le
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  calc
    _ ≤ |((c : ℝ) - b) * (z b - z a)| +
        |((b : ℝ) - a) * (z c - z b)| := abs_sub _ _
    _ = ((c : ℝ) - b) * |z b - z a| +
        ((b : ℝ) - a) * |z c - z b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
    _ ≤ ((c : ℝ) - b) * (2 * H) + ((b : ℝ) - a) * (2 * H) :=
      add_le_add (mul_le_mul_of_nonneg_left habox hp)
        (mul_le_mul_of_nonneg_left hbbox hq)
    _ = 2 * ((c : ℝ) - a) * H := by ring
    _ ≤ 2 * (k : ℝ) * H := mul_le_mul_of_nonneg_right (by linarith) hH
    _ < 1 := hsmall

/-- In a small box, the integral cross difference is exactly zero. -/
theorem cross_difference_eq_zero_of_small_box {k a b c : ℕ} {H : ℝ}
    {z : ℕ → ℝ} (hab : a < b) (hbc : b < c) (hck : c < k)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (habox : |z b - z a| ≤ 2 * H) (hbbox : |z c - z b| ≤ 2 * H)
    (hint : ∃ m : ℤ, ((c : ℝ) - b) * (z b - z a) -
      ((b : ℝ) - a) * (z c - z b) = (m : ℝ)) :
    ((c : ℝ) - b) * (z b - z a) -
      ((b : ℝ) - a) * (z c - z b) = 0 := by
  obtain ⟨m, hm⟩ := hint
  have h := abs_cross_difference_lt_one hab hbc hck hH hsmall habox hbbox
  rw [hm] at h
  have hmzero := integer_zero_of_abs_lt_one h
  simpa [hmzero] using hm

/-- Vanishing cross differences on ordered triples give one affine interpolation
on a finite set, including the empty and singleton cases. -/
theorem exists_affine_of_cross_difference_eq_zero (J : Finset ℕ) (z : ℕ → ℝ)
    (hcross : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a < b → b < c →
      ((c : ℝ) - b) * (z b - z a) -
        ((b : ℝ) - a) * (z c - z b) = 0) :
    ∃ A B : ℝ, ∀ j ∈ J, z j = A + (j : ℝ) * B := by
  by_cases hJ : J.Nonempty
  · let a := J.min' hJ
    let b := J.max' hJ
    have ha : a ∈ J := Finset.min'_mem J hJ
    have hb : b ∈ J := Finset.max'_mem J hJ
    have hmin (j : ℕ) (hj : j ∈ J) : a ≤ j := Finset.min'_le J j hj
    have hmax (j : ℕ) (hj : j ∈ J) : j ≤ b := Finset.le_max' J j hj
    by_cases hab : a = b
    · refine ⟨z a, 0, ?_⟩
      intro j hj
      have hja : j = a :=
        le_antisymm ((hmax j hj).trans (le_of_eq hab.symm)) (hmin j hj)
      simp [hja]
    · have hablt : a < b := lt_of_le_of_ne (hmin b hb) hab
      have hablt' : (a : ℝ) < b := by exact_mod_cast hablt
      have hd : (b : ℝ) - a ≠ 0 := ne_of_gt (sub_pos.mpr hablt')
      let B : ℝ := (z b - z a) / ((b : ℝ) - a)
      refine ⟨z a - (a : ℝ) * B, B, ?_⟩
      intro j hj
      have hscale : (z j - z a) * ((b : ℝ) - a) =
          ((j : ℝ) - a) * (z b - z a) := by
        by_cases hja : j = a
        · rw [hja]
          ring
        by_cases hjb : j = b
        · rw [hjb]
          ring
        have haj : a < j := lt_of_le_of_ne (hmin j hj) (Ne.symm hja)
        have hjb' : j < b := lt_of_le_of_ne (hmax j hj) hjb
        have hc := hcross a ha j hj b hb haj hjb'
        nlinarith only [hc]
      have hquot : z j - z a =
          ((j : ℝ) - a) * (z b - z a) / ((b : ℝ) - a) :=
        (eq_div_iff hd).2 hscale
      calc
        z j = z a + (z j - z a) := by ring
        _ = z a + ((j : ℝ) - a) * (z b - z a) / ((b : ℝ) - a) := by
          rw [hquot]
        _ = z a - (a : ℝ) * B + (j : ℝ) * B := by
          dsimp only [B]
          ring
  · refine ⟨0, 0, ?_⟩
    intro j hj
    exact (hJ ⟨j, hj⟩).elim

/-- Scalar affinity inside a box of width `2 * H`. The integer premise is the
explicit consequence of arithmetic progression modulo one. -/
theorem exists_affine_of_small_box {k : ℕ} {H : ℝ}
    (J : Finset ℕ) (z : ℕ → ℝ) (hJ : ∀ j ∈ J, j < k)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (hbox : ∀ i ∈ J, ∀ j ∈ J, |z j - z i| ≤ 2 * H)
    (hint : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a < b → b < c →
      ∃ m : ℤ, ((c : ℝ) - b) * (z b - z a) -
        ((b : ℝ) - a) * (z c - z b) = (m : ℝ)) :
    ∃ A B : ℝ, ∀ j ∈ J, z j = A + (j : ℝ) * B := by
  apply exists_affine_of_cross_difference_eq_zero J z
  intro a ha b hb c hc hab hbc
  exact cross_difference_eq_zero_of_small_box hab hbc (hJ c hc) hH hsmall
    (hbox a ha b hb) (hbox b hb c hc) (hint a ha b hb c hc hab hbc)

/-- The coordinatewise form gives a single real affine vector lift. In the
application the coordinate type is `Fin D` (or two copies of `Fin D`). -/
theorem exists_affine_of_small_box_vector {ι : Type uIndex} {k : ℕ} {H : ℝ}
    (J : Finset ℕ) (z : ℕ → ι → ℝ) (hJ : ∀ j ∈ J, j < k)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (hbox : ∀ i ∈ J, ∀ j ∈ J, ∀ d, |z j d - z i d| ≤ 2 * H)
    (hint : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a < b → b < c → ∀ d,
      ∃ m : ℤ, ((c : ℝ) - b) * (z b d - z a d) -
        ((b : ℝ) - a) * (z c d - z b d) = (m : ℝ)) :
    ∃ A B : ι → ℝ, ∀ j ∈ J, ∀ d, z j d = A d + (j : ℝ) * B d := by
  classical
  have hcoord : ∀ d : ι, ∃ A B : ℝ, ∀ j ∈ J,
      z j d = A + (j : ℝ) * B := by
    intro d
    exact exists_affine_of_small_box J (fun j => z j d) hJ hH hsmall
      (fun i hi j hj => hbox i hi j hj d)
      (fun a ha b hb c hc hab hbc => hint a ha b hb c hc hab hbc d)
  choose A B hAB using hcoord
  exact ⟨A, B, fun j hj d => hAB d j hj⟩

end QuantitativeVanDerWaerden

end OAI
