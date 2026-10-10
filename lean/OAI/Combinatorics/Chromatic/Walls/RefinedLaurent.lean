import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SeparationCoefficients
import OAI.Combinatorics.Chromatic.Walls.CenterLineSpecialization
import OAI.Combinatorics.Chromatic.Shuffle.LaurentLeading
import OAI.Combinatorics.Chromatic.Walls.LaurentLinearNaturality
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentProductNaturality

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
open ElementaryPositivity.LaurentAtInfinity
open SeparationInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma refined_inverseKernel_degreeZero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)).toRingHom
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val)=
      mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (scalarCrossKernel a L R v w).val := by
  trans mapRing (pointedTensorRestriction a c η hc θ L R hL hR v w).toRingHom
    (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val
  · apply HahnSeries.ext
    funext k
    exact degreeZero_refinedAtB a c η hc θ L R hL hR v w _
  · rw [pointed_quotientInverseKernel]
    congr 1
    exact congrArg Units.val (crossPointEval_inverseKernel_scalar a L R v w)

lemma refined_relative_laurent_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) (k : ℤ) :
    (polynomial ((restrictionRelativeB a c η hc
      ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) (firstCut L.dim R.dim) f).map
        (refinedAtB a c η hc θ L R hL hR v w).toRingHom)).coeff k ∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W := by
  by_cases hk : 0<k
  · rw [polynomial_coeff_positive _ k hk]
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W).zero_mem
  · have he : k=-((-k).toNat : ℤ) := by omega
    rw [he,polynomial_coeff]
    exact refinedAtB_relative_coeff_degreeCut a c η hc θ L R hL hR v w W f hf _

lemma refined_leading_separation_formula (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    LaurentAtInfinity.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        (separationSeries a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) f))=
      mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (scalarCrossKernel a L R v w).val *
      polynomial (lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
        (totalLeadingPolynomial a c η hc θ (.node L R) ⟨hL,hR⟩ W f)) := by
  have hm := mapRing_mul_polynomial
    (refinedAtB a c η hc θ L R hL hR v w).toRingHom
    (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val
    (restrictionRelativeB a c η hc
      ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) (firstCut L.dim R.dim) f)
  change mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
    (separationSeries a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) f)=_ at hm
  rw [hm]
  rw [weightComponent_laurent_mul a (SlopeArithmetic.slope c η) (.node L R) W _ _
    (scalarCrossKernel a L R v w).val
    (refined_relative_laurent_degreeCut a c η hc θ L R hL hR v w W f hf)
    (refined_inverseKernel_degreeZero a c η hc θ L R hL hR v w)]
  rw [refinedAtB_relative_polynomial,LaurentAtInfinity.polynomial_mapLinear,
    ←lineSpecialization_mapLinear]
  rfl

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
