import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseUniformModels
import OAI.Analysis.WeakInfiniteness.SupportedSeparation

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology InnerProductSpace ComplexOrder

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

theorem exists_separated_supported_model_any
    {γ σ : ℝ} (hσ : 0 ≤ σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (c : A) (hc : 0 ≤ c) {α : ℝ} (hα : 0 < α)
    (e : CStarMatrix (Fin n) (Fin n) A) (he : IsSelfAdjoint e)
    (U : CStarMatrix (Fin 1) (Fin n) A) (hU : U.conjTranspose*U=e)
    (V : supportedAlgebra e he) :
    ∃ w : CStarMatrix (Fin n) (Fin n) A, ‖w‖ ≤ 1 ∧
      diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)*w*
        diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)=w ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π c‖ → σ ≤ ‖matrixRepresentation π (Fin n) (V.val-w)‖ := by
  classical
  by_contra h
  push Not at h
  let B := Unitization ℂ (supportedAlgebra e he)
  let V₀ : B := Unitization.inr V
  let v : B := cstarClip V₀
  have hB : Exact B := exact_unitization_supportedAlgebra hA U e he hU
  have hmodels : FiniteContractionModelsAny B v γ := by
    intro H _ D hD
    obtain ⟨d,coord,M,hMn,hM⟩ := exists_scalar_matrix_coordinates D
    obtain ⟨w,hwn,hEw,hred⟩ := exists_uniform_reducing_model hn hpi c hc hα d M (hMn.trans_le hD)
    obtain ⟨K,π,hπc,hnear⟩ := h w hwn hEw
    obtain ⟨J,hJ,hJa⟩ := hred K π hπc
    let lam : supportedAlgebra e he →⋆ₙₐ[ℂ]
        (HilbertVector (Fin n) K →L[ℂ] HilbertVector (Fin n) K) :=
      (matrixRepresentation π (Fin n)).comp (NonUnitalStarSubalgebraClass.subtype (supportedAlgebra e he))
    let πB : B →⋆ₐ[ℂ] (HilbertVector (Fin n) K →L[ℂ] HilbertVector (Fin n) K) :=
      Unitization.starLift lam
    let J' := J.comp coord.toLinearIsometry
    let T := matrixRepresentation π (Fin n) V.val
    let W := matrixRepresentation π (Fin n) w
    have hr : W.comp J'.toContinuousLinearMap=J'.toContinuousLinearMap.comp D := by
      apply transport_reducing_coordinates coord J W D
      rwa [← hM]
    have hra : (star W).comp J'.toContinuousLinearMap=J'.toContinuousLinearMap.comp (star D) := by
      apply transport_reducing_coordinates coord J (star W) (star D)
      rw [show coord.conjStarAlgEquiv (star D)=star (coord.conjStarAlgEquiv D) from
        map_star coord.conjStarAlgEquiv.toStarAlgHom D, ← hM]
      exact hJa
    have hTW : ‖T-W‖ ≤ σ := by
      simpa only [T,W,map_sub] using hnear.le
    have hW : ‖W‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le (matrixRepresentation π (Fin n)) w).trans hwn
    have herr := clip_reducing_models T W D J' hσ hW hTW hr hra
    have hclip : πB v=cstarClip T := by
      change πB (cstarClip V₀)=cstarClip T
      rw [map_cstarClip]
      congr 1
      calc
        πB V₀ = (Unitization.starLift.symm πB) V :=
          (Unitization.starLift_symm_apply_apply πB V).symm
        _ = lam V := congrArg (fun f => f V) (Unitization.starLift.left_inv lam)
        _ = T := rfl
    refine ⟨⟨HilbertVector (Fin n) K⟩,πB,J',?_,?_⟩
    · rw [hclip]
      exact herr.1.trans hσγ
    · rw [hclip]
      exact herr.2.trans hσγ
  exact hgap B v (norm_cstarClip_le V₀) hB hmodels

end

end WeakPureInfiniteness
end

end OAI
