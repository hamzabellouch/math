import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Degree
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentFilteredMultiplication
import OAI.Combinatorics.Chromatic.Walls.LaurentScalarAction

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open HahnSeries
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma weightComponent_laurent_mul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ)
    (K F : LaurentSeries (tensor (quotientFamily a μ) T)) (q : LaurentSeries ℚ)
    (hF : ∀ k,F.coeff k∈degreeCutSubmodule a μ T W)
    (hK : mapRing (degreeZeroTensor a μ T).toRingHom K=
      mapRing (algebraMap ℚ (tensor (quotientFamily a μ) T)) q) :
    mapLinear (weightComponent a μ T W) (K*F)=
      mapRing (algebraMap ℚ (tensor (quotientFamily a μ) T)) q*
        mapLinear (weightComponent a μ T W) F := by
  let Q:=mapRing (algebraMap ℚ (tensor (quotientFamily a μ) T)) q
  have hpos : ∀ k,(K-Q).coeff k∈degreeCutSubmodule a μ T (T.doubleShift a+1) := by
    intro k
    have hh:=congrArg (fun x : LaurentSeries (tensor (quotientFamily a μ) T)=>x.coeff k) hK
    change degreeZeroTensor a μ T (K.coeff k)=Q.coeff k at hh
    rw [coeff_sub,←hh]
    exact sub_degreeZero_mem a μ T _
  have hz : mapLinear (weightComponent a μ T W) ((K-Q)*F)=0 := by
    apply HahnSeries.ext
    funext k
    change weightComponent a μ T W (((K-Q)*F).coeff k)=0
    apply degreeCut_weightComponent_zero
    have h:=coeff_mul_mem_of_pair
      (degreeCutSubmodule a μ T (T.doubleShift a+1)) (degreeCutSubmodule a μ T W)
      (degreeCutSubmodule a μ T (W+1))
      (fun x hx y hy=>by
        have hh:=degreeCut_mul a μ T (T.doubleShift a+1) W x y hx hy
        simpa only [show T.doubleShift a+1+W-T.doubleShift a=W+1 by omega] using hh)
      (K-Q) F hpos hF k
    exact h
  rw [sub_mul,map_sub] at hz
  rw [sub_eq_zero.mp hz,mapLinear_scalar_mul]
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
