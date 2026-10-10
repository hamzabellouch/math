import OAI.NumberTheory.JointDickman.Counting.CoefficientScalePower
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace OAI

/-! # Reduced rational approximation outside the major arcs -/

namespace JointDickman

/-- Real representatives of the rational arcs; translating a numerator by
an integer retains the corresponding arc on the unit circle. -/
def InRationalArc (θ Q δ : ℝ) : Prop :=
  ∃ r : ℚ, (r.den : ℝ) ≤ Q ∧ |θ-(r : ℝ)| ≤ δ

theorem minorArc_rational_approximation {θ Q X : ℝ}
    (hQ : 0 < Q) (hX : Q ≤ X) (hminor : ¬ InRationalArc θ Q (Q/X)) :
    ∃ r : ℚ, Q < (r.den : ℝ) ∧ (r.den : ℝ) ≤ X/Q ∧
      |θ-(r : ℝ)| ≤ 1/(r.den : ℝ)^2 := by
  have hX0 : 0 < X := hQ.trans_le hX
  have hratio : 1 ≤ X/Q := (le_div_iff₀ hQ).mpr (by simpa using hX)
  let n := ⌊X/Q⌋₊
  have hn : 0 < n := Nat.floor_pos.mpr hratio
  obtain ⟨r,herr,hden⟩ := Real.exists_rat_abs_sub_le_and_den_le θ hn
  have hrpos : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hden' : (r.den : ℝ) ≤ n := by exact_mod_cast hden
  have hnX : (n : ℝ) ≤ X/Q := Nat.floor_le (by positivity)
  have happrox : |θ-(r : ℝ)| ≤ Q/X := by
    refine herr.trans ?_
    calc
      _ ≤ 1/((n : ℝ)+1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have hr1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
        nlinarith
      _ ≤ 1/(X/Q) := one_div_le_one_div_of_le (by positivity)
        (Nat.lt_floor_add_one (X/Q)).le
      _ = _ := by field_simp
  refine ⟨r,?_,hden'.trans hnX,?_⟩
  · by_contra h
    exact hminor ⟨r,le_of_not_gt h,happrox⟩
  · refine herr.trans (one_div_le_one_div_of_le (by positivity) ?_)
    nlinarith

end JointDickman

end OAI
