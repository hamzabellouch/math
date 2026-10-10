import OAI.MeasureTheory.Falconer.Geometry.ScalarRationalProjection
import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientMul

namespace OAI

/-! Dividing the bounded ratio coefficients by a fixed positive integer
keeps the projection cost polynomial in the original doubling constant. -/
namespace Falconer
open scoped Pointwise

noncomputable def scalarDivideBudget (M m : ℕ) (K : ℝ) : ℝ :=
  (3584*(4*(M:ℝ)+11))*(K+5*(m+3:ℝ)*(2*K)^(m+1))^8

 theorem scalar_divide_coefficient {δ K a : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty) (M m : ℕ) (hm : 0 < m) (haM : |a| ≤ M)
    (hd : ((scalarCells δ (X+X)).card:ℝ) ≤ K*(scalarCells δ X).card)
    (ha : ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (a/(m:ℝ))*x))).card:ℝ) ≤
      scalarDivideBudget M m K*(scalarCells δ X).card := by
  let B := 5*(m+3:ℝ)*(2*K)^(m+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK' : K ≤ K+B := by linarith
  have hrec := scalar_reciprocal_integer_projection hδ X hX hd m hm
  have hrec' : ((scalarCells δ (X+X.image (fun x => (m:ℝ)⁻¹*x))).card:ℝ) ≤
      (K+B)*(scalarCells δ X).card :=
    hrec.trans (mul_le_mul_of_nonneg_right (by linarith : B ≤ K+B) (Nat.cast_nonneg _))
  have hmul := scalar_coefficient_mul hδ (by positivity : 0 ≤ K+B) X hX M haM
    (hd.trans (mul_le_mul_of_nonneg_right hK' (Nat.cast_nonneg _)))
    (ha.trans (mul_le_mul_of_nonneg_right hK' (Nat.cast_nonneg _))) hrec'
  simpa only [div_eq_mul_inv,scalarDivideBudget,B] using hmul

end Falconer

end OAI
