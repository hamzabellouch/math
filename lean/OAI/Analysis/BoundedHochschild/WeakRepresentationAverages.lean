import OAI.Analysis.BoundedHochschild.RectangularWeakCompactness
import OAI.Analysis.BoundedHochschild.RepresentedRightAverages

namespace OAI

/-! Continuity of the lifted averaging operators and of the map back to
coefficients of the original algebra. -/

noncomputable section

open Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def weakRepresentedRightAverage (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (W : H →WOT[ℂ] K) : H →WOT[ℂ] K :=
  ContinuousLinearMapWOT.ofCLM (representedRightAverage π σ m W.toCLM)

lemma weakRepresentedRightAverage_continuous (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) :
    Continuous (weakRepresentedRightAverage π σ m) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro ξ η
  have he : (fun W : H →WOT[ℂ] K => inner ℂ η (weakRepresentedRightAverage π σ m W ξ)) =
      fun W => ∑ i, inner ℂ ((π (m i)).adjoint η) (W ((σ (m i)).adjoint ξ)) := by
    funext W
    change inner ℂ η (representedRightAverage π σ m W.toCLM ξ) = _
    simp only [representedRightAverage, operatorRowAverage_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (ContinuousLinearMap.adjoint_inner_left (π (m i))
      (W ((σ (m i)).adjoint ξ)) η).symm
  rw [he]
  apply continuous_finsetSum
  intro i _
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _

def weakFactorValue (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (a : M) (W : H →WOT[ℂ] K) : H →WOT[ℂ] H :=
  ContinuousLinearMapWOT.ofCLM (L.adjoint.comp ((π a).comp W.toCLM))

lemma weakFactorValue_continuous (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (a : M) : Continuous (weakFactorValue π L a) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro ξ η
  have he : (fun W : H →WOT[ℂ] K => inner ℂ η (weakFactorValue π L a W ξ)) =
      fun W => inner ℂ ((π a).adjoint (L η)) (W ξ) := by
    funext W
    change inner ℂ η (L.adjoint ((π a) (W ξ))) = _
    rw [ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_left]
  rw [he]
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _

lemma weakRepresentedRightAverage_mem_ball (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∑ i, m i * star (m i) = 1) {D : ℝ} {W : H →WOT[ℂ] K}
    (hW : W ∈ rectangularWeakBall D) :
    weakRepresentedRightAverage π σ m W ∈ rectangularWeakBall D :=
  (representedRightAverage_norm_le π σ m hm W.toCLM).trans hW

end BoundedHochschild.KadisonRingrose

end

end OAI
