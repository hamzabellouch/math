import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGeneratorCoordinates

namespace OAI

/-! # Every finite contour vector lies in the actual generator domain

The bounded matrix generator differentiates the restricted semigroup. Its
inclusion in Y × Y differentiates the original evolution, including vectors
in nontrivial Jordan chains.
-/

open Set
open scoped NNReal

namespace DefocusingNLS

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Differentiation of the matrix exponential commutes with the inclusion
of the finite contour space in the ambient Banach space. -/
theorem projectionSemigroup_generator_domain (S : ℝ≥0 → E →L[ℂ] E)
    (Q : E →L[ℂ] E) (hcomm : ∀ t, Commute (S t) Q)
    (hfin : FiniteDimensional ℂ Q.range) (G : Q.range →L[ℂ] Q.range)
    (hG : ∀ t, projectionSemigroupRestriction S Q hcomm t =
      NormedSpace.exp ((t : ℝ) • G)) (w : Q.range) :
    HasDerivWithinAt (fun t : ℝ => S t.toNNReal (w : E))
      (G w : E) (Ici 0) 0 := by
  let : FiniteDimensional ℂ Q.range := hfin
  let : CompleteSpace Q.range := FiniteDimensional.complete ℂ Q.range
  let A := (ContinuousLinearMap.apply ℂ Q.range w).restrictScalars ℝ
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • G) w) (G w) 0 := by
    have h := A.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) G 0)
    simpa only [Function.comp_def, A, zero_smul, NormedSpace.exp_zero, one_mul,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply] using h
  let J := Q.range.subtypeL.restrictScalars ℝ
  have hj : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • G) w : E)) (G w : E) 0 := by
    exact J.hasFDerivAt.comp_hasDerivAt 0 hd
  apply hj.hasDerivWithinAt.congr
  · intro t ht
    have he := congrArg (fun L : Q.range →L[ℂ] Q.range => (L w : E)) (hG t.toNNReal)
    simpa only [projectionSemigroupRestriction_apply, Real.coe_toNNReal t ht] using he
  · have he := congrArg (fun L : Q.range →L[ℂ] Q.range => (L w : E)) (hG 0)
    simpa only [projectionSemigroupRestriction_apply, Real.toNNReal_zero, NNReal.coe_zero] using he

end Abstract

/-- Both real coordinates of an arbitrary complexified generator vector
satisfy the exact bounded-potential perturbation identity. -/
theorem homogeneous_generator_free_coordinates (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k)
    (w z : HomogeneousY a k × HomogeneousY a k)
    (hw : HasDerivWithinAt (fun t : ℝ =>
      homogeneousComplexLinearizedStep a b k ha ha1 hk m q t.toNNReal w) z (Ici 0) 0) :
    let X := homogeneousComplexReal a k ha ha1 hk
    let Y := homogeneousComplexImag a k ha ha1 hk
    let B := homogeneousLinearizedPotential a k ha ha1 hk m q
    HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk (X w))
      (X z - B (X w)) (Ici 0) 0 ∧
    HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk (Y w))
      (Y z - B (Y w)) (Ici 0) 0 := by
  dsimp only
  have hX := (homogeneousComplexReal a k ha ha1 hk).hasFDerivAt.comp_hasDerivWithinAt 0 hw
  have hY := (homogeneousComplexImag a k ha ha1 hk).hasFDerivAt.comp_hasDerivWithinAt 0 hw
  have hx : HasDerivWithinAt (fun t : ℝ =>
      homogeneousLinearizedStep a b k ha ha1 hk m q t.toNNReal
        (homogeneousComplexReal a k ha ha1 hk w))
      (homogeneousComplexReal a k ha ha1 hk z) (Ici 0) 0 := by
    simpa only [Function.comp_def, homogeneousComplexLinearizedStep,
      homogeneousComplexification_real] using hX
  have hy : HasDerivWithinAt (fun t : ℝ =>
      homogeneousLinearizedStep a b k ha ha1 hk m q t.toNNReal
        (homogeneousComplexImag a k ha ha1 hk w))
      (homogeneousComplexImag a k ha ha1 hk z) (Ici 0) 0 := by
    simpa only [Function.comp_def, homogeneousComplexLinearizedStep,
      homogeneousComplexification_imag] using hY
  exact ⟨homogeneousFree_derivWithin_of_linearized a b k ha ha1 hk m q _ _ hx,
    homogeneousFree_derivWithin_of_linearized a b k ha ha1 hk m q _ _ hy⟩

end DefocusingNLS

end OAI
