import OAI.Probability.InvariantIsing.Haar.HaarCurveTangent
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialValue
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Integrating the coordinate-plane gradient bound along an orthogonal curve. -/
noncomputable section
open Matrix MvPolynomial Set
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomial_curve_bound {N : ℕ} (p : MatrixPolynomial N)
    (U : ℝ → SpecialOrthogonal N) (B : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (K δ : ℝ) (hδ : 0 ≤ δ)
    (hB : ∀ t ∈ Icc (0:ℝ) 1, ∀ i j,
      HasDerivAt (fun s => (U s : Matrix (Fin N) (Fin N) ℝ) i j) (B t i j) t)
    (hK : ∀ t ∈ Icc (0:ℝ) 1,
      (∑ i, ∑ j, |(B t*(U t : Matrix (Fin N) (Fin N) ℝ).transpose) i j|) ≤ K)
    (hp : ∀ V : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) V ≤ δ^2) :
    |haarPolynomialValue p (U 1)-haarPolynomialValue p (U 0)| ≤ K*δ/2 := by
  let f' := fun t => matrixPolynomialEval (U t : Matrix (Fin N) (Fin N) ℝ)
    (matrixPolynomialDerivation (B t*(U t : Matrix (Fin N) (Fin N) ℝ).transpose) p)
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun s => haarPolynomialValue p (U s)) (f' t) t :=
    orthogonalCurve_polynomial_derivative p U (B t) t (hB t ht)
  have hb (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) : ‖f' t‖ ≤ K*δ/2 := by
    have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hx := matrixPolynomial_direction_bound p
      (U t : Matrix (Fin N) (Fin N) ℝ)
      (B t*(U t : Matrix (Fin N) (Fin N) ℝ).transpose)
      (orthogonalCurve_tangent_skew U (B t) t (hB t ht')) δ hδ (hp (U t))
    have hy := mul_le_mul_of_nonneg_right (hK t ht') hδ
    change |f' t| ≤ K*δ/2
    dsimp [f'] at *
    linarith
  simpa only [Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht => (hd t ht).hasDerivWithinAt) hb

end InvariantIsing

end

end OAI
