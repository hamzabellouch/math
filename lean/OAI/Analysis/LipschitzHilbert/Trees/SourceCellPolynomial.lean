import OAI.Analysis.LipschitzHilbert.Trees.SourceBoxSupremum
import OAI.Analysis.LipschitzHilbert.Estimates.BoxPolynomialWeight

namespace OAI

/-! Polynomial weights on the actual transverse cells of a tree.
The exponent is kept symbolic so the fixed high order need not expand. -/
noncomputable section
namespace LipschitzHilbert

theorem transverse_cell_polynomial_lower (b W n y : ℝ) (q : ℕ)
    (hW : 0<W) (hy : |y-b-n*W|≤W/2) :
    ((1+|n|)^2/32)^q≤polynomialWeight b (2*W) q y := by
  have hy' : |y-(b+n*W)|≤2*W := by
    have he : y-(b+n*W)=y-b-n*W := by ring
    rw [he]
    linarith
  have h := box_polynomial_weight (b+n*W) (2*W) (-n/2) y q (by positivity) hy'
  have hc : b+n*W+(2*W)*(-n/2)=b := by ring
  rw [hc] at h
  apply le_trans _ h
  apply pow_le_pow_left₀ (by positivity)
  rw [abs_div,abs_neg]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [abs_nonneg n]

theorem transverse_cell_polynomial_weight (b W n y : ℝ) (q : ℕ)
    (hW : 0<W) (hy : |y-b-n*W|≤W/2) :
    (1+|n|)^(2*q)≤32^q*polynomialWeight b (2*W) q y := by
  have h := transverse_cell_polynomial_lower b W n y q hW hy
  rw [div_pow,←pow_mul] at h
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0<(32:ℝ)^q)).mp h

/-- Multiplication by the transverse polynomial supplies the precise
power needed to absorb the density loss on that cell. -/
theorem transverse_cell_weighted_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b W n y : ℝ) (q : ℕ) (hW : 0<W) (hy : |y-b-n*W|≤W/2) (v : E) :
    (1+|n|)^(2*q)*‖v‖≤32^q*‖polynomialWeight b (2*W) q y • v‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg
    ((polynomialWeight_one_le b (2*W) q y).trans' (by norm_num))]
  have h := mul_le_mul_of_nonneg_right (transverse_cell_polynomial_weight b W n y q hW hy) (norm_nonneg v)
  simpa only [mul_assoc] using h

/-- Squaring gives the exponent `4q` in the cell-supremum energy. -/
theorem transverse_cell_weighted_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b W n y : ℝ) (q : ℕ) (hW : 0<W) (hy : |y-b-n*W|≤W/2) (v : E) :
    (1+|n|)^(4*q)*‖v‖^2≤32^(2*q)*‖polynomialWeight b (2*W) q y • v‖^2 := by
  have h := pow_le_pow_left₀ (by positivity : 0≤(1+|n|)^(2*q)*‖v‖)
    (transverse_cell_weighted_norm b W n y q hW hy v) 2
  simp only [mul_pow,←pow_mul] at h
  convert h using 1 <;> congr 2 <;> omega

end LipschitzHilbert

end

end OAI
