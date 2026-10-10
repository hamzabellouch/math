import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixCovarianceAlgebra
import OAI.Probability.SKBarriers.Hierarchy.BlockCovarianceComparison

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def matrixInner (d : ℕ) (Q R : Fin d → Fin d → ℝ) : ℝ := ∑ a, ∑ b, Q a b*R a b

def matrixSquare (d : ℕ) (Q : Fin d → Fin d → ℝ) : ℝ := ∑ a, ∑ b, (Q a b)^2

theorem matrixSquare_sub (d : ℕ) (R Q : Fin d → Fin d → ℝ) :
    matrixSquare d (fun a b => R a b-Q a b)=matrixSquare d R-2*matrixInner d Q R+matrixSquare d Q := by
  simp only [matrixSquare,matrixInner,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem matrixSquare_nonneg (d : ℕ) (R : Fin d → Fin d → ℝ) : 0  ≤  matrixSquare d R :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem matrixCovariance_lower (d : ℕ) (R Q : Fin d → Fin d → ℝ) :
    -matrixSquare d Q  ≤  matrixSquare d R-2*matrixInner d Q R := by
  have H := matrixSquare_nonneg d (fun a b => R a b-Q a b)
  rw [matrixSquare_sub] at H
  linarith

def factorPath (d r k : ℕ) (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (j : Fin (k+1)) (a b : Fin d) : ℝ :=
  ∑ l, if l ≤ j then factorCovariance d r (B l) a b else 0

theorem factorPath_last (d r k : ℕ) (B : Fin (k+1) → Fin r → Fin d → ℝ) (a b : Fin d) :
    factorPath d r k B (Fin.last k) a b=∑ l, factorCovariance d r (B l) a b := by
  simp only [factorPath,Fin.le_last,ite_true]

theorem factorPath_inner (d r k : ℕ) (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (j : Fin (k+1)) (R : Fin d → Fin d → ℝ) :
    matrixInner d (factorPath d r k B j) R=
      ∑ l, if l ≤ j then matrixInner d (factorCovariance d r (B l)) R else 0 := by
  simp only [matrixInner,factorPath,Finset.sum_mul,ite_mul,zero_mul]
  calc
    _ = ∑ a, ∑ l, ∑ b, if l ≤ j then factorCovariance d r (B l) a b*R a b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, if l ≤ j then factorCovariance d r (B l) a b*R a b else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> simp only [Finset.sum_const_zero]

section
variable {S : Type} [Fintype S] [Nonempty S]

def matrixHamiltonianObservables (N d : ℕ) (β : ℝ) (X : S → Fin N → Fin d → ℝ) :
    Fin (N*N) → S → ℝ := fun u s => matrixPairFeature N d β (X s) (finProdFinEquiv.symm u)

def matrixFieldObservables (N d r k : ℕ) (β : ℝ) (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (X : S → Fin N → Fin d → ℝ) : Fin (k+1) → Fin (N*r) → S → ℝ :=
  fun l u s => matrixFieldFeature N d r β (B l) (X s) (finProdFinEquiv.symm u)

omit [Fintype S] [Nonempty S] in
theorem matrixHamiltonianObservables_covariance {N d : ℕ} (hN : 0<N) (β : ℝ)
    (X : S → Fin N → Fin d → ℝ) (s t : S) :
    (∑ u, matrixHamiltonianObservables N d β X u s*matrixHamiltonianObservables N d β X u t)=
      ((N:ℝ)*β^2/2)*matrixSquare d (replicaCrossOverlap N d (X s) (X t)) := by
  unfold matrixHamiltonianObservables
  rw [← finProdFinEquiv.sum_comp]
  simpa only [Equiv.symm_apply_apply,matrixSquare] using matrixPairFeature_covariance hN β (X s) (X t)

omit [Fintype S] [Nonempty S] in
theorem matrixFieldObservables_covariance {N d r k : ℕ} (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
    (l : Fin (k+1)) (s t : S) :
    (∑ u, matrixFieldObservables N d r k β B X l u s*matrixFieldObservables N d r k β B X l u t)=
      ((N:ℝ)*β^2)*matrixInner d (factorCovariance d r (B l)) (replicaCrossOverlap N d (X s) (X t)) := by
  unfold matrixFieldObservables
  rw [← finProdFinEquiv.sum_comp]
  simpa only [Equiv.symm_apply_apply,matrixInner] using matrixFieldFeature_covariance β (B l) (X s) (X t)

omit [Fintype S] [Nonempty S] in
theorem matrixFieldObservables_prefix {N d r k : ℕ} (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
    (j : Fin (k+1)) (s t : S) :
    (∑ l, if l ≤ j then ∑ u, matrixFieldObservables N d r k β B X l u s*
      matrixFieldObservables N d r k β B X l u t else 0)=
      ((N:ℝ)*β^2)*matrixInner d (factorPath d r k B j) (replicaCrossOverlap N d (X s) (X t)) := by
  simp_rw [matrixFieldObservables_covariance,factorPath_inner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

theorem matrixFiniteInterpolation {N d r k : ℕ} (hN : 0<N) (hr : 0<r) (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
    (D : Fin d → Fin d → ℝ) (hself : ∀ s, replicaCrossOverlap N d (X s) (X s)=D)
    (c : S → ℝ) (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    let n:=blockDimension (N*N) (N*r) k
    let H:=matrixHamiltonianObservables N d β X
    let F:=matrixFieldObservables N d r k β B X
    let m:=weightedBlockMass (N*N) (N*r) k w
    let I:=blockInterpolationChoice (N*N) (N*r) k
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 1))) 0  ≤
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 0))) 0+
      ((N:ℝ)*β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
        ∑ j, w j*matrixSquare d (factorPath d r k B j)) := by
  let K : ℝ := (N:ℝ)*β^2/4
  have hK : 0 ≤ K := by positivity
  have H := blockObservable_compare (Nat.mul_pos hN hr)
    (matrixHamiltonianObservables N d β X) (matrixFieldObservables N d r k β B X) c w hw hs
    (K*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D))
    (fun j => K*matrixSquare d (factorPath d r k B j))
    (fun s => by
      simp only [pow_two]
      rw [matrixHamiltonianObservables_covariance hN]
      have HF := matrixFieldObservables_prefix β B X (Fin.last k) s s
      simp only [Fin.le_last,ite_true] at HF
      rw [HF,hself s]
      dsimp only [K]
      ring_nf
      exact le_rfl)
    (fun j s t => by
      rw [matrixHamiltonianObservables_covariance hN,matrixFieldObservables_prefix]
      have HK := mul_le_mul_of_nonneg_left (matrixCovariance_lower d (replicaCrossOverlap N d (X s) (X t))
        (factorPath d r k B j)) hK
      dsimp only [K] at HK ⊢
      nlinarith)
  have he : (∑ j, w j*(K*matrixSquare d (factorPath d r k B j)))=
      K*∑ j, w j*matrixSquare d (factorPath d r k B j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at H
  dsimp only
  convert H using 1
  dsimp only [K]
  ring

end
end SK.Analytic

end
end

end OAI
