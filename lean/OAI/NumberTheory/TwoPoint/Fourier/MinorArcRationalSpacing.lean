import OAI.NumberTheory.TwoPoint.Fourier.MinorArcCircleKernel
import Mathlib.RingTheory.Coprime.Basic

namespace OAI

/-! Separation of a nonintegral rational point, and stability under the
small perturbation used in the minor-arc rational approximation. -/

namespace TwoPointCorrelations

lemma minor_arc_circle_norm_le (x : ℝ) : ‖(x : UnitAddCircle)‖ ≤ |x| := by
  rw [UnitAddCircle.norm_eq]
  simpa using round_le x (0 : ℤ)

lemma minor_arc_rational_norm {a q : ℤ} (hq : 0 < q) (hqa : ¬q ∣ a) :
    1 / (q : ℝ) ≤ ‖(((a : ℝ) / (q : ℝ)) : UnitAddCircle)‖ := by
  let j := round ((a : ℝ) / (q : ℝ))
  have hz : a - j * q ≠ 0 := by
    intro he
    apply hqa
    refine ⟨j, ?_⟩
    have hh : a = j * q := sub_eq_zero.mp he
    simpa only [mul_comm] using hh
  have hb : (1 : ℝ) ≤ |(a : ℝ) - (j : ℝ) * q| := by
    exact_mod_cast Int.one_le_abs hz
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  rw [UnitAddCircle.norm_eq]
  have he : |(a : ℝ) / (q : ℝ) - (j : ℝ)| = |(a : ℝ) - (j : ℝ) * q| / (q : ℝ) := by
    calc
      _ = |((a : ℝ) - (j : ℝ) * q) / (q : ℝ)| := by congr 1; field_simp
      _ = _ := by rw [abs_div, abs_of_pos hqr]
  change 1 / (q : ℝ) ≤ |(a : ℝ) / (q : ℝ) - (j : ℝ)|
  rw [he]
  exact div_le_div_of_nonneg_right hb hqr.le

lemma minor_arc_perturbed_rational {a q : ℤ} {x : ℝ} (hq : 0 < q) (hqa : ¬q ∣ a)
    (hx : |x - (a : ℝ) / (q : ℝ)| ≤ 1 / (2 * (q : ℝ))) :
    1 / (2 * (q : ℝ)) ≤ ‖(x : UnitAddCircle)‖ := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hrat := minor_arc_rational_norm hq hqa
  have herr := (minor_arc_circle_norm_le (x - (a : ℝ) / (q : ℝ))).trans hx
  rw [AddCircle.coe_sub] at herr
  have ht := norm_le_norm_add_norm_sub (x : UnitAddCircle) (((a : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)
  have he : 1 / (q : ℝ) = 2 * (1 / (2 * (q : ℝ))) := by field_simp
  rw [he] at hrat
  linarith

lemma minor_arc_multiple_spacing {α : ℝ} {a q k : ℤ} (hq : 0 < q)
    (hqak : ¬q ∣ a * k) (hk : |(k : ℝ)| ≤ (q : ℝ) / 2)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    1 / (2 * (q : ℝ)) ≤ ‖(((k : ℝ) * α : ℝ) : UnitAddCircle)‖ := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  apply minor_arc_perturbed_rational hq hqak
  calc
    |(k : ℝ) * α - ((a * k : ℤ) : ℝ) / (q : ℝ)| =
        |(k : ℝ)| * |α - (a : ℝ) / (q : ℝ)| := by
      rw [← abs_mul]
      congr 1
      push_cast
      ring
    _ ≤ ((q : ℝ) / 2) * (1 / (q : ℝ) ^ 2) :=
      mul_le_mul hk happrox (abs_nonneg _) (by positivity)
    _ = 1 / (2 * (q : ℝ)) := by field_simp

lemma minor_arc_pair_spacing {α : ℝ} {a q m n : ℤ} (hq : 0 < q)
    (hcop : IsCoprime q a) (hmn : m ≠ n)
    (hshort : |((m - n : ℤ) : ℝ)| ≤ (q : ℝ) / 2)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    1 / (2 * (q : ℝ)) ≤ dist (((m : ℝ) * α : ℝ) : UnitAddCircle)
      (((n : ℝ) * α : ℝ) : UnitAddCircle) := by
  have hk : m - n ≠ 0 := sub_ne_zero.mpr hmn
  have hnot : ¬q ∣ a * (m - n) := by
    intro hh
    have hd := hcop.dvd_of_dvd_mul_left hh
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hle := Int.natAbs_le_of_dvd_ne_zero hd hk
    have hlei : |q| ≤ |m - n| := by
      rw [← Int.natCast_natAbs q, ← Int.natCast_natAbs (m - n)]
      exact_mod_cast hle
    rw [abs_of_pos hq] at hlei
    have hler : (q : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by exact_mod_cast hlei
    linarith
  have h := minor_arc_multiple_spacing hq hnot hshort happrox
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  convert h using 1
  congr 2
  push_cast
  ring

end TwoPointCorrelations

end OAI
