import OAI.Probability.InvariantIsing.Haar.HaarHeatLinear

namespace OAI

/-! Exact preservation of Haar means by the polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

def haarPolynomialMean {N : ℕ} (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ] :
    MatrixPolynomial N →ₗ[ℝ] ℝ where
  toFun p := ∫ U, haarPolynomialValue p U ∂μ
  map_add' p q := by
    change (∫ U, matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) (p+q) ∂μ) = _
    simp only [map_add]
    exact integral_add (haarPolynomialValue_integrable p μ) (haarPolynomialValue_integrable q μ)
  map_smul' c p := by
    change (∫ U, matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) (c • p) ∂μ) = _
    simp only [map_smul]
    exact integral_smul c _

lemma haarPolynomialMean_laplacian {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : MatrixPolynomial N) :
    haarPolynomialMean μ (haarPolynomialLaplacian N p) = 0 := by
  rw [haarPolynomialLaplacian_apply,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  exact integral_haarPolynomialDerivation μ (matrixPolynomialDerivation (planeGenerator i j) p) i j

theorem haarPolynomialHeat_mean {N d : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : haarPolynomialSpace N d) (t : ℝ) :
    (∫ U, haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∂μ) =
      ∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ := by
  let f (s : ℝ) := haarPolynomialMean μ
    ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)
  have hd (s : ℝ) : HasDerivAt f 0 s := by
    have h := haarPolynomialHeat_linear_hasDerivAt (haarPolynomialMean μ) p s
    rw [haarPolynomialMean_laplacian] at h
    exact h
  have he : f t=f 0 := is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  change haarPolynomialMean μ _ = haarPolynomialMean μ _
  simpa only [f,haarPolynomialHeat_zero] using he

end InvariantIsing

end

end OAI
