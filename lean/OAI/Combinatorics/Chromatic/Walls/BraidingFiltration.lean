import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CellTransferSeparation
import OAI.Combinatorics.Chromatic.Walls.TripleSymbols
import OAI.Combinatorics.Chromatic.GradedAlgebra.CenterCoefficientMembership

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open SplitTree SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.CenterCalculus
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance braidTensorCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidTensorAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidTensorNUSemiring (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) :=
  (braidTensorCommRing a μ d e).toNonUnitalNonAssocSemiring

lemma refinedAtB_mem_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    refinedAtB a c η hc θ L R hL hR v w x∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W := by
  have he := refinedCenterPolynomial_eval a c η hc θ L R hL hR (Sum.elim v w) x
  change evalRat (Sum.elim v w) (refinedCenterPolynomial a c η hc θ L R hL hR x)=
    refinedAtB a c η hc θ L R hL hR v w x at he
  rw [←he]
  exact evalRat_mem_of_coeff _ _
    (refinedCenterPolynomial_coeff_degreeCut a c η hc θ L R hL hR W x hx) _

lemma braidingRatio_refined_leading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (F : LaurentSeries (B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) R.dim))
    (hF : ∀ k,F.coeff k∈sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    LaurentAtInfinity.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        ((braidingRatioUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val*F))=
    LaurentAtInfinity.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom F) := by
  rw [map_mul]
  have h := weightComponent_laurent_mul a (SlopeArithmetic.slope c η) (.node L R) W
    (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
      (braidingRatioUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val)
    (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom F) 1
    (fun k=>refinedAtB_mem_degreeCut a c η hc θ L R hL hR v w W _ (hF k))
    (by rw [map_one]; exact refined_braidingRatio_degreeZero a c η hc θ hχ L R hL hR v w)
  simpa only [map_one,one_mul] using h

theorem braidingRatio_coeff_next (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (W : ℤ)
    (F : LaurentSeries (B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e))
    (hF : ∀ k,F.coeff k∈sourceTensorFiltration a c η hc θ d e W) (k : ℤ) :
    ((braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val*F-F).coeff k∈
      sourceTensorFiltration a c η hc θ d e (W+1) := by
  apply tensor_leading_restrictions_detect a c η hc θ d e W
  · rw [HahnSeries.coeff_sub]
    apply Submodule.sub_mem _ _ (hF k)
    rw [mul_comm]
    exact coeff_mul_mem (sourceTensorFiltrationIdeal a c η hc θ d e W) F _ hF k
  · rintro ⟨L,hoL,hL,hd,j,z⟩ ⟨R,hoR,hR,he,l,w⟩ hjl
    subst d
    subst e
    apply refinedAtB_weight_zero_test a c η hc θ L R hL hR W
    · intro v w
      have hh := congrArg (fun S : LaurentSeries
        (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))=>S.coeff k)
        (braidingRatio_refined_leading a c η hc θ hχ L R hL hR v w W F hF)
      change weightComponent a (SlopeArithmetic.slope c η) (.node L R) W
        (refinedAtB a c η hc θ L R hL hR v w _)=_ at hh
      rw [HahnSeries.coeff_sub,map_sub,map_sub,sub_eq_zero]
      exact hh
    · change (2*L.totalDegree j+L.doubleShift a)+(2*R.totalDegree l+R.doubleShift a)=W at hjl
      change 2*(L.totalDegree j+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W
      omega

end ElementaryPositivity.RawShuffle

end

end OAI
