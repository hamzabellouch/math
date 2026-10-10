import Mathlib
import OAI.Probability.SKRatio.Matrices.MatrixEntryCLM
import OAI.Probability.SKRatio.Matrices.GaussianProductIntegral
import OAI.Probability.SKRatio.Matrices.IntegralProductDeviation

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
namespace SKRatioGaussian
open Matrix Real MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem goe_inverse_loop_centered {r : ℝ} (hr : 0 ≤ r) (B : Matrix ι ι ℝ) (i : ι)
    {K : Matrix ι ι ℝ → Matrix ι ι ℝ} {L T : ℝ≥0} {C : ℝ}
    {s : Set (MatrixCoordinates ι → ℝ)}
    (hK : LipschitzWith L K) (hC : ∀ M, opNorm (K M) ≤ C)
    (hT : LipschitzWith T (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) =>
      Matrix.trace (K (goeMatrix r g)*B))) (hT0 : 0 < T)
    (hs : MeasurableSet s)
    (hder : ∀ g ∈ s, ∀ b, HasDerivAt
      (fun t : ℝ => K (goeMatrix r g+t • symmetricElementary i b) b i)
      ((K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i) 0) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    let Lπ : ℝ≥0 := L*(⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
    |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-
      r*(∫ g, Matrix.trace (K (goeMatrix r g)*B) ∂μ)*(∫ g, K (goeMatrix r g) i i ∂μ)| ≤
      (Fintype.card ι:ℝ)*(sqrt (2*r)*(Lπ:ℝ)+r*(2*C*opNorm B*C))*μ.real sᶜ+
        r*(C*((2*exp (π^2/8))*(T:ℝ))+C*opNorm B*C) := by
  intro μ Lπ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hcomp : LipschitzWith Lπ (fun g => K (goeMatrix r g)) :=
    hK.comp (goeMatrix_pi_lipschitz r)
  have hf (a b : ι) : LipschitzWith Lπ (fun g => K (goeMatrix r g) a b) := by
    simpa only [one_mul] using! (matrixEntry_lipschitz a b).comp hcomp
  have hc (g : MatrixCoordinates ι → ℝ) (a b : ι) :
      ‖K (goeMatrix r g) a b‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using (matrix_entry_le_opNorm _ a b).trans (hC _)
  have hd (g : MatrixCoordinates ι → ℝ) (b : ι) :
      ‖(K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i‖ ≤
        2*C*opNorm B*C := by
    have he : ‖(K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i‖ ≤
        ‖K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)‖ := by
      simpa only [Real.norm_eq_abs] using!
        matrix_entry_le_frobenius (K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i
    apply he.trans
    apply (matrix_inverse_diff_bound _ _ _).trans
    calc
      _ ≤ C*(opNorm B*2)*C := by
        exact mul_le_mul
          (mul_le_mul (hC _) (mul_le_mul_of_nonneg_left (symmetricElementary_norm_le i b) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC0)
          (hC _) (norm_nonneg _) (mul_nonneg hC0 (mul_nonneg (norm_nonneg _) (by norm_num)))
      _ = _ := by ring
  have hz (g : MatrixCoordinates ι → ℝ) :
      ‖∑ b, (K (goeMatrix r g)*B) b i*K (goeMatrix r g) b i‖ ≤ C*opNorm B*C := by
    rw [Real.norm_eq_abs]
    apply (goe_cross_contraction_bound _ _ _).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)) (hC _)
      (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
  have hzi : Integrable (fun g => ∑ b, (K (goeMatrix r g)*B) b i*K (goeMatrix r g) b i) μ :=
    Integrable.mono' (integrable_const (C*opNorm B*C)) (by
      have hc := hcomp.continuous
      exact (continuous_finsetSum _ (fun b _ =>
        ((hc.mul continuous_const).matrix_elem b i).mul (hc.matrix_elem b i))).aestronglyMeasurable)
      (ae_of_all _ hz)
  have hi : Integrable (fun g => Matrix.trace (K (goeMatrix r g)*B)) μ :=
    gaussianProduct_integrable_lipschitz hT
  have ht : (∫ g, |Matrix.trace (K (goeMatrix r g)*B)-
      ∫ h, Matrix.trace (K (goeMatrix r h)*B) ∂μ| ∂μ) ≤ (2*exp (π^2/8))*(T:ℝ) :=
    gaussianProduct_centered_L1 hT hT0
  exact integral_loop_deviation hr hi (hf i i).continuous.aestronglyMeasurable
    (ae_of_all _ (fun g => hc g i i)) hzi (ae_of_all _ hz) ht
    (goe_inverse_loop_raw hr B i hf hc hd hs hder)

end SKRatioGaussian

noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology

end
end
end
end
end
end
end
end

end OAI
