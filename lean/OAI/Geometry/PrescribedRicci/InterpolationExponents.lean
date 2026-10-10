import Mathlib

namespace OAI

/-! Interpolation Exponents. -/

noncomputable section
open scoped ENNReal
namespace TameInterpolation

def exponent (m j : ℕ) : ℝ≥0∞ := (ENNReal.ofReal ((j:ℝ)/(2*(m:ℝ))))⁻¹

lemma exponent_zero (m : ℕ) : exponent m 0 = ∞ := by simp [exponent]

lemma exponent_of_pos {m j : ℕ} (hm : 0 < m) (hj : 0 < j) :
    exponent m j = ENNReal.ofReal (2*(m:ℝ)/(j:ℝ)) := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hj' : 0 < (j:ℝ) := by exact_mod_cast hj
  rw [exponent,← ENNReal.ofReal_inv_of_pos (div_pos hj' (by positivity))]
  congr 1
  field_simp

lemma holder_inverse (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.HolderTriple (ENNReal.ofReal a)⁻¹ (ENNReal.ofReal b)⁻¹ (ENNReal.ofReal (a+b))⁻¹ := by
  constructor
  simp only [inv_inv,ENNReal.ofReal_add ha hb]

lemma exponent_middle_gt {m j : ℕ} (hj : j+1 < m) : 2 < 2*(m:ℝ)/((j+1:ℕ):ℝ) := by
  have hj' : 0 < ((j+1:ℕ):ℝ) := by positivity
  apply (lt_div_iff₀ hj').mpr
  have hh : ((j+1:ℕ):ℝ) < (m:ℝ) := by exact_mod_cast hj
  linarith only [hh]

lemma exponent_holder_step {m j : ℕ} (hj : j+1 < m) :
    ENNReal.HolderTriple (exponent m j) (exponent m (j+2))
      (ENNReal.ofReal (2/(2*(m:ℝ)/((j+1:ℕ):ℝ)) ))⁻¹ := by
  have hm : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hj0 : (j+1:ℝ) ≠ 0 := by positivity
  have he : 2/(2*(m:ℝ)/((j+1:ℕ):ℝ)) = (j:ℝ)/(2*(m:ℝ))+((j+2:ℕ):ℝ)/(2*(m:ℝ)) := by
    push_cast
    field_simp
    ring
  rw [he]
  exact holder_inverse _ _ (by positivity) (by positivity)

lemma interpolation_holder_conjugate {p : ℝ} (hp : 2 < p) :
    ENNReal.HolderTriple (ENNReal.ofReal (2/p))⁻¹ (ENNReal.ofReal ((p-2)/p))⁻¹ 1 := by
  constructor
  simp only [inv_inv,inv_one,← ENNReal.ofReal_add (by positivity : 0 ≤ 2/p) (by positivity : 0 ≤ (p-2)/p)]
  rw [show 2/p+(p-2)/p = 1 by field_simp; ring]
  exact ENNReal.ofReal_one

lemma interpolation_power_exponent {p : ℝ} (hp : 2 < p) :
    (ENNReal.ofReal ((p-2)/p))⁻¹ * ENNReal.ofReal (p-2) = ENNReal.ofReal p := by
  have hp0 : 0 < p := by linarith only [hp]
  have hp2 : 0 < p-2 := by linarith only [hp]
  rw [← ENNReal.ofReal_inv_of_pos (div_pos hp2 hp0),← ENNReal.ofReal_mul (inv_nonneg.mpr (div_nonneg hp2.le hp0.le))]
  congr 1
  field_simp
end TameInterpolation

end

end OAI
