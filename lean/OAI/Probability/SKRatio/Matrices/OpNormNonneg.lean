import Mathlib
import OAI.Probability.SKRatio.Matrices.LinEquiv

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
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKRatioGaussian.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_nonneg (M : Matrix ι ι ℂ) : 0 ≤ opNorm M := norm_nonneg _
lemma opNorm_add (M N : Matrix ι ι ℂ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  change ‖linEquiv (M+N)‖ ≤ _
  rw [(linEquiv (ι := ι)).map_add]
  exact norm_add_le _ _
lemma opNorm_sub (M N : Matrix ι ι ℂ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖lin (M-N)‖ ≤ _
  have hh : lin (M-N) = lin M-lin N := linEquiv.map_sub M N
  rw [hh]
  exact norm_sub_le _ _
lemma opNorm_mul (M N : Matrix ι ι ℂ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  change ‖lin (M*N)‖ ≤ _
  rw [lin_mul]
  exact norm_mul_le _ _
lemma opNorm_neg (M : Matrix ι ι ℂ) : opNorm (-M) = opNorm M := by
  change ‖lin (-M)‖ = _
  have hh : lin (-M) = -lin M := linEquiv.map_neg M
  rw [hh,norm_neg]
  rfl
lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  rw [opNorm,lin_one]
  exact ContinuousLinearMap.norm_id_le

lemma sandwich_frobenius (D E : Matrix ι ι ℂ) :
    ‖D*E*D‖ ≤ opNorm D^2*‖E‖ := by
  calc
    _ ≤ ‖D*E‖*opNorm D := frobenius_mul_le_opNorm_right _ _
    _ ≤ (opNorm D*‖E‖)*opNorm D := mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _)
    _ = _ := by ring

lemma sandwich_opNorm (D E : Matrix ι ι ℂ) :
    opNorm (D*E*D) ≤ opNorm D^2*opNorm E := by
  calc
    _ ≤ opNorm (D*E)*opNorm D := opNorm_mul _ _
    _ ≤ (opNorm D*opNorm E)*opNorm D := mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _)
    _ = _ := by ring

lemma sandwich_difference_frobenius (D D' E : Matrix ι ι ℂ) :
    ‖D*E*D-D'*E*D'‖ ≤ (opNorm D+opNorm D')*opNorm (D-D')*‖E‖ := by
  have he : D*E*D-D'*E*D' = (D-D')*E*D+D'*E*(D-D') := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(D-D')*E*D‖+‖D'*E*(D-D')‖ := norm_add_le _ _
    _ ≤ (opNorm (D-D')*‖E‖)*opNorm D+(opNorm D'*‖E‖)*opNorm (D-D') := by
      apply add_le_add
      · exact (frobenius_mul_le_opNorm_right _ _).trans
          (mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _))
      · exact (frobenius_mul_le_opNorm_right _ _).trans
          (mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _))
    _ = _ := by ring

lemma sandwich_difference_opNorm (D D' E : Matrix ι ι ℂ) :
    opNorm (D*E*D-D'*E*D') ≤ (opNorm D+opNorm D')*opNorm (D-D')*opNorm E := by
  have he : D*E*D-D'*E*D' = (D-D')*E*D+D'*E*(D-D') := by noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm ((D-D')*E*D)+opNorm (D'*E*(D-D')) := opNorm_add _ _
    _ ≤ (opNorm (D-D')*opNorm E)*opNorm D+(opNorm D'*opNorm E)*opNorm (D-D') := by
      apply add_le_add
      · exact (opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _))
      · exact (opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _))
    _ = _ := by ring

lemma product_four_point (a b c d e f g h : Matrix ι ι ℂ) :
    ‖(a*e-b*f)-(c*g-d*h)‖ ≤
      ‖(a-b)-(c-d)‖*opNorm e + ‖c-d‖*opNorm (e-g) +
      opNorm (b-d)*‖e-f‖ + opNorm d*‖(e-f)-(g-h)‖ := by
  have he : (a*e-b*f)-(c*g-d*h) =
      ((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)+d*((e-f)-(g-h)) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)‖+‖d*((e-f)-(g-h))‖ := norm_add_le _ _
    _ ≤ (‖((a-b)-(c-d))*e+(c-d)*(e-g)‖+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖((a-b)-(c-d))*e‖+‖(c-d)*(e-g)‖)+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
      gcongr
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm _ _
      · exact frobenius_mul_le_opNorm _ _

end SKRatioGaussian.ComplexMatrix

end
end
end
end
end
end
end
end
end

end OAI
