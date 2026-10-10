import OAI.Analysis.KadisonKastler.ProjectionMatrices

namespace OAI

/-!
# The centered label map

The covariance matrix of the centered diagonal projections in a
normalized matrix trace is `d⁻¹ I - d⁻² 11*`. It is the scalar multiple
of the projection off the constant vectors constructed below.
-/

namespace KadisonKastler

open Finset

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance centeredLabelsOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance centeredLabelsStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

def constantLabelProjection : CStarMatrix ι ι ℂ :=
  CStarMatrix.ofMatrix (fun _ _ => (Fintype.card ι : ℂ)⁻¹)

omit [DecidableEq ι] in
@[simp]
theorem constantLabelProjection_apply (i j : ι) :
    constantLabelProjection i j = (Fintype.card ι : ℂ)⁻¹ := rfl

omit [DecidableEq ι] in
theorem constantLabelProjection_isStarProjection [Nonempty ι] :
    IsStarProjection (constantLabelProjection (ι := ι)) := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · change constantLabelProjection * constantLabelProjection = constantLabelProjection (ι := ι)
    apply CStarMatrix.ext
    intro i j
    simp only [CStarMatrix.mul_apply, constantLabelProjection_apply, sum_const,
      card_univ, nsmul_eq_mul]
    field_simp
  · change star (constantLabelProjection (ι := ι)) = constantLabelProjection
    apply CStarMatrix.ext
    intro i j
    simp [CStarMatrix.star_apply]

def centeredLabelProjection : CStarMatrix ι ι ℂ := 1 - constantLabelProjection

theorem centeredLabelProjection_isStarProjection [Nonempty ι] :
    IsStarProjection (centeredLabelProjection (ι := ι)) :=
  constantLabelProjection_isStarProjection.one_sub

/-- The label map has the `d⁻¹/²` scale used at every free-word cut. -/
def centeredLabelMatrix : CStarMatrix ι ι ℂ :=
  (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) • centeredLabelProjection

theorem norm_centeredLabelMatrix_le [Nonempty ι] :
    ‖centeredLabelMatrix (ι := ι)‖ ≤ (Real.sqrt (Fintype.card ι : ℝ))⁻¹ := by
  rw [centeredLabelMatrix, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    _ ≤ (Real.sqrt (Fintype.card ι : ℝ))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left
        (IsStarProjection.norm_le _ centeredLabelProjection_isStarProjection)
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := mul_one _

@[simp]
theorem centeredLabelProjection_apply (i j : ι) :
    centeredLabelProjection i j = (if i = j then 1 else 0) - (Fintype.card ι : ℂ)⁻¹ := by
  simp [centeredLabelProjection, CStarMatrix.one_apply]

theorem centeredLabelProjection_mul_self [Nonempty ι] :
    centeredLabelProjection (ι := ι) * centeredLabelProjection = centeredLabelProjection :=
  centeredLabelProjection_isStarProjection.isIdempotentElem.eq

end

end KadisonKastler

end OAI
