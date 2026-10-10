import OAI.Analysis.BoundedHochschild.PositiveKernelMatrices

namespace OAI

/-! Hilbert-space compression preserves complete positivity. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H K I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype I]

lemma operatorMatrix_nonneg_of_quadratic
    (B : CStarMatrix I I (H →L[ℂ] H))
    (hB : ∀ ξ : I → H, 0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (B i j (ξ j))) : 0 ≤ B := by
  let ρ := WeakPureInfiniteness.matrixOperatorHom (n := I) (H := H)
  apply (NonUnitalStarAlgHom.map_le_map_iff ρ
    WeakPureInfiniteness.matrixOperator_injective).mp
  rw [map_zero, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro ξ
  have hp : 0 ≤ inner ℂ ξ (ρ B ξ) := by
    change 0 ≤ inner ℂ ξ (WeakPureInfiniteness.matrixOperator B ξ)
    simpa only [WeakPureInfiniteness.matrixOperator_apply, PiLp.inner_apply, inner_sum]
      using hB ξ
  have hq : 0 ≤ inner ℂ (ρ B ξ) ξ := by
    rw [← inner_conj_symm (𝕜 := ℂ) (ρ B ξ) ξ]
    exact star_nonneg_iff.mpr hp
  exact ⟨Complex.ext (by simp) hq.2, hq.1⟩

def compressCompletelyPositive (φ : CompletelyPositiveMap A (K →L[ℂ] K))
    (V : H →L[ℂ] K) : CompletelyPositiveMap A (H →L[ℂ] H) where
  toFun a := V.adjoint.comp ((φ a).comp V)
  map_add' a b := by ext ξ; simp
  map_smul' z a := by ext ξ; simp
  map_cstarMatrix_nonneg' n B hB := by
    apply operatorMatrix_nonneg_of_quadratic
    intro ξ
    change 0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (V.adjoint (φ (B i j) (V (ξ j))))
    simp only [ContinuousLinearMap.adjoint_inner_right]
    exact operatorMatrix_quadratic_nonneg (B.map φ) (φ.map_cstarMatrix_nonneg B hB)
      (fun i => V (ξ i))

@[simp] lemma compressCompletelyPositive_apply
    (φ : CompletelyPositiveMap A (K →L[ℂ] K)) (V : H →L[ℂ] K) (a : A) :
    compressCompletelyPositive φ V a = V.adjoint.comp ((φ a).comp V) := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
