import OAI.Probability.InvariantIsing.Haar.HaarHeatConstants

namespace OAI

/-! Uniform order bounds for the polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial Set
namespace InvariantIsing

theorem haarPolynomialHeat_bounds {N d : ℕ} (p : haarPolynomialSpace N d)
    (a b : ℝ)
    (ha : ∀ U : SpecialOrthogonal N, a ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    (hb : ∀ U : SpecialOrthogonal N, haarPolynomialValue (p : MatrixPolynomial N) U ≤ b)
    {t : ℝ} (ht : 0 ≤ t) (U : SpecialOrthogonal N) :
    haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∈ Icc a b := by
  let onep : haarPolynomialSpace N d := ⟨1,one_mem_haarPolynomialSpace N d⟩
  have h1 : haarPolynomialHeat N d t onep = onep := haarPolynomialHeat_one N d t
  have hscalar (c : ℝ) (V : SpecialOrthogonal N) :
      matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
        ((c • onep : haarPolynomialSpace N d) : MatrixPolynomial N) = c := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
      (c • (1 : MatrixPolynomial N)) = c
    rw [map_smul,map_one]
    exact mul_one c
  have hl : ∀ V : SpecialOrthogonal N,
      0 ≤ haarPolynomialValue ((p-a • onep : haarPolynomialSpace N d) : MatrixPolynomial N) V := by
    intro V
    change 0 ≤ matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ) (_-_)
    rw [map_sub,hscalar]
    exact sub_nonneg.mpr (ha V)
  have hu : ∀ V : SpecialOrthogonal N,
      0 ≤ haarPolynomialValue ((b • onep-p : haarPolynomialSpace N d) : MatrixPolynomial N) V := by
    intro V
    change 0 ≤ matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ) (_-_)
    rw [map_sub,hscalar]
    exact sub_nonneg.mpr (hb V)
  have hlow := haarPolynomialHeat_nonneg (p-a • onep) hl ht U
  have hupp := haarPolynomialHeat_nonneg (b • onep-p) hu ht U
  rw [map_sub,map_smul,h1] at hlow hupp
  change 0 ≤ matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) (_-_) at hlow hupp
  rw [map_sub,hscalar] at hlow hupp
  exact ⟨sub_nonneg.mp hlow,sub_nonneg.mp hupp⟩

end InvariantIsing

end

end OAI
