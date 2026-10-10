import OAI.Analysis.KadisonKastler.RectangularHilbert

namespace OAI

/-! # Adjoint and product formulas for rectangular operator matrices -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

local instance rectangularOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance rectangularOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace H] [Fintype l] in
theorem rectangularHilbertMatrix_mul
    (M : CStarMatrix l m (H →L[ℂ] H)) (N : CStarMatrix m n (H →L[ℂ] H)) :
    rectangularHilbertMatrix (M * N) =
      (rectangularHilbertMatrix M).comp (rectangularHilbertMatrix N) := by
  ext x i
  simp only [rectangularHilbertMatrix_apply, ContinuousLinearMap.comp_apply,
    CStarMatrix.mul_apply, sum_apply, mul_apply_eq_comp, map_sum]
  rw [Finset.sum_comm]

theorem rectangularHilbertMatrix_conjTranspose (M : CStarMatrix m n (H →L[ℂ] H)) :
    rectangularHilbertMatrix M.conjTranspose = (rectangularHilbertMatrix M).adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply,
    rectangularHilbertMatrix_apply, CStarMatrix.conjTranspose_apply, inner_sum, sum_inner,
    ContinuousLinearMap.star_eq_adjoint]
  rw [Finset.sum_comm]

theorem norm_rectangular_star (M : CStarMatrix m n (H →L[ℂ] H)) : ‖M.conjTranspose‖ = ‖M‖ := by
  rw [← norm_rectangularHilbertMatrix, rectangularHilbertMatrix_conjTranspose,
    LinearIsometryEquiv.norm_map, norm_rectangularHilbertMatrix]

theorem norm_rectangular_mul_star [DecidableEq m]
    (M : CStarMatrix m n (H →L[ℂ] H)) : ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 := by
  rw [← norm_rectangularHilbertMatrix, rectangularHilbertMatrix_mul,
    rectangularHilbertMatrix_conjTranspose]
  have h := ContinuousLinearMap.norm_adjoint_comp_self (rectangularHilbertMatrix M).adjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map,
    norm_rectangularHilbertMatrix, pow_two] using h

/-- The adjoint of a partial isometry has the same norm on a vector as its
range projection. -/
theorem norm_rectangular_star_apply_of_projection [DecidableEq m]
    (V : CStarMatrix m n (H →L[ℂ] H))
    (hV : IsStarProjection (V * V.conjTranspose)) (z : Generator.FiniteHilbert m H) :
    ‖rectangularHilbertMatrix V.conjTranspose z‖ = ‖rectangularHilbertMatrix (V * V.conjTranspose) z‖ := by
  let T := rectangularHilbertMatrix V
  let P := rectangularHilbertMatrix (V * V.conjTranspose)
  have hP : IsStarProjection P := hV.map (hilbertMatrixHom (H := H) (n := m))
  have hPT : P = T.comp T.adjoint := by
    exact (rectangularHilbertMatrix_mul _ _).trans (by rw [rectangularHilbertMatrix_conjTranspose])
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [rectangularHilbertMatrix_conjTranspose]
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
  change Complex.re (inner ℂ (T.adjoint.adjoint (T.adjoint z)) z) =
    Complex.re (inner ℂ (P.adjoint (P z)) z)
  rw [ContinuousLinearMap.adjoint_adjoint]
  have hstar : P.adjoint = P := hP.isSelfAdjoint.star_eq
  have hmul : P.comp P = P := hP.isIdempotentElem.eq
  rw [hstar]
  change Complex.re (inner ℂ ((T.comp T.adjoint) z) z) =
    Complex.re (inner ℂ ((P.comp P) z) z)
  rw [hmul, ← hPT]

end

end KadisonKastler

end OAI
