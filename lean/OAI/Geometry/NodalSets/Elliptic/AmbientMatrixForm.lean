import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Matrix.PosDef
import OAI.Geometry.NodalSets.Elliptic.TargetEmbedding

namespace OAI

namespace Yau.Target
open Manifold Matrix ContinuousLinearMap
open scoped ContDiff
noncomputable section

def ambientMatrixForm (A : Matrix (Fin 5) (Fin 5) ℝ) :
    AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • ((innerSL ℝ (EuclideanSpace.basisFun (Fin 5) ℝ i)).smulRight
    (innerSL ℝ (EuclideanSpace.basisFun (Fin 5) ℝ j)))

lemma ambientMatrixForm_apply (A : Matrix (Fin 5) (Fin 5) ℝ) (v w : AmbientBase) :
    ambientMatrixForm A v w = ∑ i, ∑ j, v i * A i j * w j := by
  simp [ambientMatrixForm, EuclideanSpace.inner_single_left,mul_comm,mul_assoc]

lemma ambientMatrixForm_symm (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.IsHermitian)
    (v w : AmbientBase) : ambientMatrixForm A v w = ambientMatrixForm A w v := by
  rw [ambientMatrixForm_apply,ambientMatrixForm_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := hA.apply i j
  simp only [star_trivial] at h
  rw [h]
  ring

lemma ambientMatrixForm_pos (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (v : AmbientBase) (hv : v ≠ 0) : 0 < ambientMatrixForm A v v := by
  have hn : (fun i ↦ v i) ≠ 0 := by
    intro he
    apply hv
    ext i
    exact congrFun he i
  have hh := hA.dotProduct_mulVec_pos hn
  rw [ambientMatrixForm_apply]
  simpa [dotProduct,mulVec,Finset.mul_sum,mul_assoc] using hh

lemma ambientMatrixForm_smooth (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j)) :
    ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞
      (fun x ↦ ambientMatrixForm (A x)) := by
  unfold ambientMatrixForm
  apply ContMDiff.sum
  intro i _
  apply ContMDiff.sum
  intro j _
  exact (hA i j).smul contMDiff_const

end
end Yau.Target

end OAI
