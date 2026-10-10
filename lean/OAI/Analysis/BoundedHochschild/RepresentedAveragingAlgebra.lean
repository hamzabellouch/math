import OAI.Analysis.BoundedHochschild.WeakRepresentationAverages
import OAI.Analysis.BoundedHochschild.RightAveragingAlgebra

namespace OAI

/-! Composition and reindexing of the lifted finite right averages. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M I J H K : Type*} [CStarAlgebra M] [Fintype I] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma representedRightAverage_reindex (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : I ≃ J) (m : J → M) (W : H →L[ℂ] K) :
    representedRightAverage π σ (m ∘ e) W = representedRightAverage π σ m W := by
  apply ContinuousLinearMap.ext
  intro ξ
  simpa only [representedRightAverage, operatorRowAverage_apply, Function.comp_apply] using
    e.sum_comp (fun j => π (m j) (W ((σ (m j)).adjoint ξ)))

lemma representedRightAverage_comp (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (n : J → M) (W : H →L[ℂ] K) :
    representedRightAverage π σ m (representedRightAverage π σ n W) =
      representedRightAverage π σ (fun p : I × J => m p.1 * n p.2) W := by
  classical
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [representedRightAverage, operatorRowAverage_apply, Fintype.sum_prod_type,
    map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change π (m i) (π (n j) (W ((σ (n j)).adjoint ((σ (m i)).adjoint ξ)))) =
    (π (m i) * π (n j)) (W ((σ (m i) * σ (n j)).adjoint ξ))
  rw [show σ (m i) * σ (n j) = (σ (m i)).comp (σ (n j)) from rfl,
    ContinuousLinearMap.adjoint_comp]
  rfl

lemma representedRightAverage_one (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →L[ℂ] K) :
    representedRightAverage π σ (fun _ : Fin 1 => (1 : M)) W = W := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [representedRightAverage, operatorRowAverage_apply, Fin.sum_univ_one,
    map_one, ContinuousLinearMap.adjoint_one, one_apply_eq_self]

end BoundedHochschild.KadisonRingrose

end

end OAI
