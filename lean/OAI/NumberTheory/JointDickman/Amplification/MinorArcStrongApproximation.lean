import OAI.NumberTheory.JointDickman.Amplification.MinorArcApproximation

namespace OAI

/-! # Dirichlet approximation retaining the error on the ambient scale -/
namespace JointDickman

theorem minorArc_strong_rational_approximation {θ Q X : ℝ}
    (hQ : 0 < Q) (hX : Q ≤ X) (hminor : ¬ InRationalArc θ Q (Q/X)) :
    ∃ r : ℚ, Q < (r.den:ℝ) ∧ (r.den:ℝ) ≤ X/Q ∧ |θ-(r:ℝ)| ≤ 1/X := by
  have hX0 : 0 < X := hQ.trans_le hX
  have hratio : 1 ≤ X/Q := (le_div_iff₀ hQ).mpr (by simpa using hX)
  let n := ⌊X/Q⌋₊
  have hn : 0 < n := Nat.floor_pos.mpr hratio
  obtain ⟨r,herr,hden⟩ := Real.exists_rat_abs_sub_le_and_den_le θ hn
  have hrpos : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hden' : (r.den:ℝ) ≤ n := by exact_mod_cast hden
  have hnX : (n:ℝ) ≤ X/Q := Nat.floor_le (by positivity)
  have hnlarge : X/Q < (n:ℝ)+1 := Nat.lt_floor_add_one (X/Q)
  have happrox : |θ-(r:ℝ)| ≤ Q/X := by
    refine herr.trans ?_
    calc
      _ ≤ 1/((n:ℝ)+1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have hr1 : (1:ℝ) ≤ r.den := by exact_mod_cast r.pos
        nlinarith
      _ ≤ 1/(X/Q) := one_div_le_one_div_of_le (by positivity) hnlarge.le
      _ = _ := by field_simp
  have hrlo : Q < (r.den:ℝ) := by
    by_contra h
    exact hminor ⟨r,le_of_not_gt h,happrox⟩
  refine ⟨r,hrlo,hden'.trans hnX,herr.trans ?_⟩
  apply one_div_le_one_div_of_le hX0
  have hscaled : X < Q*((n:ℝ)+1) := by
    simpa only [mul_comm] using (div_lt_iff₀ hQ).mp hnlarge
  nlinarith

end JointDickman

end OAI
