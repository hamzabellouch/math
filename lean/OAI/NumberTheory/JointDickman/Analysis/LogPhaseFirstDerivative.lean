import OAI.NumberTheory.JointDickman.Amplification.DiscreteFirstDerivative

namespace OAI

/-! # A first-derivative bound for short logarithmic phase sums -/
namespace JointDickman
open Finset Problem337

lemma log_step_bounds {x : ℝ} (hx : 0 < x) :
    1/(x+1) ≤ Real.log (x+1)-Real.log x ∧
      Real.log (x+1)-Real.log x ≤ 1/x := by
  have hx1 : 0 < x+1 := by positivity
  rw [← Real.log_div hx1.ne' hx.ne']
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx)
    convert h using 1
    field_simp
    ring
  · have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx)
    convert h using 1
    field_simp
    ring

lemma log_step_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log (y+1)-Real.log y ≤ Real.log (x+1)-Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← Real.log_div (by positivity : x+1 ≠ 0) hx.ne',
    ← Real.log_div (by positivity : y+1 ≠ 0) hy.ne']
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hy hx).mpr
  nlinarith

/-- Below the first stationary range the sharp logarithmic sum is bounded
by the reciprocal frequency, with no length-dependent error. -/
theorem positive_log_phase_first_bound {U Z : ℝ} (hU : 1 ≤ U)
    (hZ : 0 < Z) (hZU : Z ≤ U/4) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤ 8*U/Z := by
  have hU0 : 0 < U := by linarith
  have hβ : 0 < Z/(4*U) := by positivity
  have hd (i : ℕ) (hiL : L ≤ i) (hiR : i ≤ R) :
      Z/(4*U) ≤ Z*Real.log ((i+1:ℕ):ℝ)-Z*Real.log (i:ℝ) ∧
      Z*Real.log ((i+1:ℕ):ℝ)-Z*Real.log (i:ℝ) ≤ 1-Z/(4*U) := by
    have hi : U ≤ (i:ℝ) := hL.trans (by exact_mod_cast hiL)
    have hi2 : (i:ℝ) ≤ 2*U := (by exact_mod_cast hiR : (i:ℝ) ≤ R).trans hR
    have hi0 : (0:ℝ) < i := hU0.trans_le hi
    obtain ⟨hlo,hhi⟩ := log_step_bounds hi0
    push_cast
    rw [← mul_sub]
    constructor
    · apply (div_le_div_of_nonneg_left hZ.le (by positivity : (0:ℝ) < i+1)
        (by linarith : (i:ℝ)+1 ≤ 4*U)).trans
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlo hZ.le
    · have hu : Z*((1:ℝ)/i) ≤ Z/U := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left hZ.le hU0 hi
      have hh : Z/U ≤ 1/4 := (div_le_iff₀ hU0).mpr (by linarith)
      have hb : Z/(4*U) ≤ 1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hhi hZ.le]
  have hmono : AntitoneOn (fun i : ℕ => Z*Real.log ((i+1:ℕ):ℝ)-
      Z*Real.log (i:ℝ)) (Set.Icc L R) := by
    intro i hi j _ hij
    push_cast
    rw [← mul_sub, ← mul_sub]
    apply mul_le_mul_of_nonneg_left _ hZ.le
    exact log_step_antitone (hU0.trans_le (hL.trans (by exact_mod_cast hi.1)))
      (by exact_mod_cast hij)
  have hh := ExponentialSum.first_derivative_sum_bound_Icc
    (fun n => Z*Real.log (n:ℝ)) L R (Z/(4*U)) 0 hβ
    (fun i hiL hiR => by simpa using (hd i hiL hiR).1)
    (fun i hiL hiR => by simpa using (hd i hiL hiR).2) (Or.inr hmono)
  convert hh using 1
  field_simp
  norm_num

end JointDickman

end OAI
