import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CrossPolynomiality
import OAI.Combinatorics.Chromatic.Walls.CenterLineNaturality

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma crossKernel_leading_polynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    ∃ p : Polynomial (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)),
      mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (scalarCrossKernel a L R v w).val *
      polynomial (lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
        (totalLeadingPolynomial a c η hc θ (.node L R) ⟨hL,hR⟩ W f)) = polynomial p := by
  obtain ⟨q,hq⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ (.node L R) ⟨hL,hR⟩
    W f hf (crossPairs L R) (crossPairs_ne L R) (crossPairs_norev L R)
      (crossPairs_symmetric a c η θ hχ L R hL hR)
  refine ⟨(crossPolynomial a L R v w Int.toNat).map
    (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))) *
    lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0)) q, ?_⟩
  rw [hq,map_mul,lineSpecialization_map_algebra,centerDenominator_crossPairs_line,
    map_mul,←polynomial_map,←mul_assoc,←map_mul,scalarCrossKernel_denominator,
    polynomial_map,map_mul]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
