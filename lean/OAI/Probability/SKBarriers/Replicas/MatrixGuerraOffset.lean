import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixGuerraKernel

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

variable {S : Type} [Fintype S] [Nonempty S]

theorem matrixFiniteInterpolation_offset {M N d r k : ℕ} (hN : 0<N) (hr : 0<r) (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
    (H : Fin M → S → ℝ) (C : ℝ)
    (hcov : ∀ s t, (∑ u, H u s*H u t)=
      ((N:ℝ)*β^2/2)*matrixSquare d (replicaCrossOverlap N d (X s) (X t))-C)
    (D : Fin d → Fin d → ℝ) (hself : ∀ s, replicaCrossOverlap N d (X s) (X s)=D)
    (c : S → ℝ) (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    let n:=blockDimension M (N*r) k
    let F:=matrixFieldObservables N d r k β B X
    let m:=weightedBlockMass M (N*r) k w
    let I:=blockInterpolationChoice M (N*r) k
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 1))) 0 ≤
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 0))) 0+
      ((N:ℝ)*β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
        ∑ j, w j*matrixSquare d (factorPath d r k B j)) := by
  let K : ℝ := (N:ℝ)*β^2/4
  have hK : 0 ≤ K := by positivity
  have HC := blockObservable_compare (Nat.mul_pos hN hr) H
    (matrixFieldObservables N d r k β B X) c w hw hs
    (K*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D)-C/2)
    (fun j => K*matrixSquare d (factorPath d r k B j)+C/2)
    (fun s => by
      simp only [pow_two]
      rw [hcov]
      have HF := matrixFieldObservables_prefix β B X (Fin.last k) s s
      simp only [Fin.le_last,ite_true] at HF
      rw [HF,hself s]
      dsimp only [K]
      ring_nf
      exact le_rfl)
    (fun j s t => by
      rw [hcov,matrixFieldObservables_prefix]
      have HK := mul_le_mul_of_nonneg_left (matrixCovariance_lower d (replicaCrossOverlap N d (X s) (X t))
        (factorPath d r k B j)) hK
      dsimp only [K] at HK ⊢
      nlinarith)
  have he : (∑ j, w j*(K*matrixSquare d (factorPath d r k B j)+C/2))=
      K*∑ j, w j*matrixSquare d (factorPath d r k B j)+C/2 := by
    simp_rw [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at HC
  dsimp only
  convert HC using 1
  dsimp only [K]
  ring

end SK.Analytic

end
end

end OAI
