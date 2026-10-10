import OAI.Analysis.FiniteFactor.CrossedProduct.FieldRepresentation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceFiberVector_basis (n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceFiberVector (sourceBasis n) x = lp.single 2 n (1 : ℂ) := by
  filter_upwards [sourceFiberVector_coe (sourceBasis n), source_ae_all_fibers (sourceBasis_coe n)]
    with x hf hb
  apply Subtype.ext
  funext k
  rw [hf, hb]
  by_cases hk : k = n
  · subst k; simp [lp.single_apply]
  · simp [lp.single_apply, hk]

theorem sourceOperatorField_mul (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A * B) x = sourceOperatorField A x * sourceOperatorField B x := by
  have h (n : ℤ) : ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A * B) x (lp.single 2 n (1 : ℂ)) =
        sourceOperatorField A x (sourceOperatorField B x (lp.single 2 n (1 : ℂ))) := by
    filter_upwards [sourceOperatorField_represents θ (mul_mem hA hB) (sourceBasis n),
      sourceOperatorField_represents θ hA (B (sourceBasis n)),
      sourceOperatorField_represents θ hB (sourceBasis n), sourceFiberVector_basis n]
      with x hab ha hb he
    rw [he] at hab hb
    change sourceFiberVector (A (B (sourceBasis n))) x = _ at hab
    rw [ha, hb] at hab
    exact hab.symm
  filter_upwards [ae_all_iff.mpr h] with x hx
  apply fiberOperator_ext
  intro k n
  exact congrArg (fun v : SourceFiberHilbert => v k) (hx n)

theorem sourceOperatorField_one (θ : SourceCoordinate → ℝ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField (1 : SourceHilbert SourceCoordinate →L[ℂ]
      SourceHilbert SourceCoordinate) x = 1 := by
  have h (n : ℤ) : ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (1 : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
        x (lp.single 2 n (1 : ℂ)) = lp.single 2 n 1 := by
    filter_upwards [sourceOperatorField_represents θ (one_mem (sourceAlgebra θ)) (sourceBasis n),
      sourceFiberVector_basis n] with x hi he
    change sourceFiberVector (sourceBasis n) x = _ at hi
    rw [he] at hi
    exact hi.symm
  filter_upwards [ae_all_iff.mpr h] with x hx
  apply fiberOperator_ext
  intro k n
  exact congrArg (fun v : SourceFiberHilbert => v k) (hx n)

theorem fiberOperator_star_entry (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (k n : ℤ) :
    ((star A) (lp.single 2 n (1 : ℂ))) k = star ((A (lp.single 2 k (1 : ℂ))) n) := by
  calc
    _ = inner ℂ (lp.single 2 k (1 : ℂ)) ((star A) (lp.single 2 n (1 : ℂ))) := by
      rw [lp.inner_single_left]; simp
    _ = inner ℂ (A (lp.single 2 k (1 : ℂ))) (lp.single 2 n (1 : ℂ)) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = _ := by rw [lp.inner_single_right]; simp [RCLike.inner_apply]

theorem sourceOperatorField_star (θ : SourceCoordinate → ℝ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField (star A) x = star (sourceOperatorField A x) := by
  have hs : ∀ᵐ x ∂sourceBaseMeasure, ∀ k n : ℤ,
      sourceMatrixEntry (star A) k n x = star (sourceMatrixEntry A n k x) := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    exact sourceMatrixEntry_star θ hA k
  filter_upwards [sourceOperatorField_entries_ae θ hA,
    sourceOperatorField_entries_ae θ (star_mem hA), hs] with x ha hstar hs
  apply fiberOperator_ext
  intro k n
  rw [hstar, fiberOperator_star_entry, ha, hs]

theorem sourceOperatorField_zero (x : SourceCoordinate → ℝ) :
    sourceOperatorField (0 : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) x = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using sourceOperatorField_norm 0 x) (norm_nonneg _)

theorem sourceOperatorField_sub (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A - B) x = sourceOperatorField A x - sourceOperatorField B x := by
  have hsub : ∀ᵐ x ∂sourceBaseMeasure, ∀ n k : ℤ,
      sourceMatrixEntry (A-B) k n x = sourceMatrixEntry A k n x - sourceMatrixEntry B k n x := by
    rw [ae_all_iff]
    intro n
    exact source_ae_all_fibers (Lp.coeFn_sub (A (sourceBasis n)) (B (sourceBasis n)))
  filter_upwards [sourceOperatorField_entries_ae θ hA, sourceOperatorField_entries_ae θ hB,
    sourceOperatorField_entries_ae θ (sub_mem hA hB), hsub] with x ha hb hab hs
  apply fiberOperator_ext
  intro k n
  change (sourceOperatorField (A-B) x (lp.single 2 n (1 : ℂ))) k =
    (sourceOperatorField A x (lp.single 2 n (1 : ℂ))) k -
      (sourceOperatorField B x (lp.single 2 n (1 : ℂ))) k
  rw [hab, ha, hb, hs]

/-- Every projection in the source algebra yields an actual measurable
orthogonal-projection field. -/
theorem sourceOperatorField_projection (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) :
    ∀ᵐ x ∂sourceBaseMeasure, IsStarProjection (sourceOperatorField p x) := by
  filter_upwards [sourceOperatorField_mul θ hp hp, sourceOperatorField_star θ hp] with x hm hs
  refine ⟨?_, ?_⟩
  · change sourceOperatorField p x * sourceOperatorField p x = sourceOperatorField p x
    rw [← hm, hproj.isIdempotentElem]
  · change star (sourceOperatorField p x) = sourceOperatorField p x
    rw [← hs, hproj.isSelfAdjoint.star_eq]

/-- The original invariant-projection equation holds fiberwise for the actual
operator and projection fields. -/
theorem sourceOperatorField_invariant (θ : SourceCoordinate → ℝ)
    {p T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hT : T ∈ sourceAlgebra θ)
    (hinv : (1-p)*T*p = 0) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (1-sourceOperatorField p x)*sourceOperatorField T x*sourceOperatorField p x = 0 := by
  have hsub := sub_mem (one_mem (sourceAlgebra θ)) hp
  filter_upwards [sourceOperatorField_mul θ (mul_mem hsub hT) hp,
    sourceOperatorField_mul θ hsub hT, sourceOperatorField_sub θ (one_mem (sourceAlgebra θ)) hp,
    sourceOperatorField_one θ] with x hab ha hs h1
  rw [hinv, sourceOperatorField_zero, ha, hs, h1] at hab
  exact hab.symm

/-- The normal trace already proved is exactly the field-integral formula. -/
theorem sourceVacuumFunctional_fieldIntegral (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    sourceVacuumFunctional H = ∫ x,
      (sourceOperatorField H x (lp.single 2 0 (1 : ℂ))) 0 ∂sourceBaseMeasure := by
  rw [sourceVacuumFunctional_matrixIntegral]
  apply integral_congr_ae
  filter_upwards [sourceOperatorField_entries_ae θ hH] with x hx
  exact (hx 0 0).symm

end
end FiniteFactor

end OAI
