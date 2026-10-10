import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixGuerraKernel
import OAI.Probability.SKBarriers.Hierarchy.BlockSiteFields

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

variable {A S : Type} [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]

def matrixSiteWeight {d : ℕ} (Λ : Fin d → Fin d → ℝ) (v : A → Fin d → ℝ) (a : A) : ℝ :=
  ∑ u, ∑ t, Λ u t*v a u*v a t

omit [Fintype A] [Nonempty A] [Fintype S] [Nonempty S] in
theorem matrixSiteWeight_sum {N d : ℕ} (Λ : Fin d → Fin d → ℝ) (v : A → Fin d → ℝ)
    (e : S → Fin N → A) (s : S) :
    (∑ i, matrixSiteWeight Λ v (e s i))=(N:ℝ)*matrixInner d Λ (replicaCrossOverlap N d (fun i => v (e s i)) (fun i => v (e s i))) := by
  by_cases hN : N=0
  · subst N; simp
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN
  simp only [matrixSiteWeight,matrixInner,replicaCrossOverlap,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  field_simp [hNr]

def matrixSiteVector {d r k : ℕ} (β : ℝ) (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (v : A → Fin d → ℝ) (j : Fin ((k+1)*r)) (a : A) : ℝ :=
  β*∑ u, B (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 u*v a u

omit [Fintype A] [Nonempty A] [Fintype S] [Nonempty S] in
theorem matrixSiteVector_observables {N d r k : ℕ} (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (v : A → Fin d → ℝ) (e : S → Fin N → A) :
    matrixFieldObservables N d r k β B (fun s i => v (e s i))=
      fun b p s => siteBlockObservables (matrixSiteVector β B v) b p (e s) := by
  funext b p s
  simp only [matrixFieldObservables,matrixFieldFeature,siteBlockObservables,matrixSiteVector,
    Equiv.symm_apply_apply]

theorem matrixGuerra_factor {N d r k : ℕ} (hN : 0<N) (hr : 0<r) (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (v : A → Fin d → ℝ)
    (e : S → Fin N → A) (he : Function.Injective e)
    (D Λ : Fin d → Fin d → ℝ)
    (hself : ∀ s, replicaCrossOverlap N d (fun i => v (e s i)) (fun i => v (e s i))=D)
    (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    (∫ z, affineLogPartition (fun _ : S => 0)
      (fun s => coordinateLinear (N*N) (fun u => matrixHamiltonianObservables N d β (fun s i => v (e s i)) u s))
      z ∂fiberGaussian (N*N) 0)/(N:ℝ) ≤
      vectorHierarchy ((k+1)*r) (siteBlockMass r k w) (matrixSiteVector β B v)
        (siteValueTerminal (matrixSiteWeight Λ v)) 0 - matrixInner d Λ D+
        (β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
          ∑ j, w j*matrixSquare d (factorPath d r k B j)) := by
  let X : S → Fin N → Fin d → ℝ := fun s i => v (e s i)
  let c : S → ℝ := fun s => ∑ i, matrixSiteWeight Λ v (e s i)
  let n:=blockDimension (N*N) (N*r) k
  let H:=matrixHamiltonianObservables N d β X
  let F:=matrixFieldObservables N d r k β B X
  let m:=weightedBlockMass (N*N) (N*r) k w
  let I:=blockInterpolationChoice (N*N) (N*r) k
  have hc : c=fun _ => (N:ℝ)*matrixInner d Λ D := by
    funext s
    rw [show c s=∑ i, matrixSiteWeight Λ v (e s i) from rfl,matrixSiteWeight_sum,hself s]
  have hinter := matrixFiniteInterpolation hN hr β B X D hself c w hw hs
  change hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
    (interpolationCoefficient n I 1))) 0 ≤ _ at hinter
  rw [hc,affineLogPartition_const_weight,hierarchyPressure_add_const n m
    (affineLogPartition_boundedDerivs (fun _ : S => 0) _) ((N:ℝ)*matrixInner d Λ D)] at hinter
  dsimp only at hinter
  rw [blockObservable_root_one] at hinter
  have hz := siteBlock_root_zero_le hN e he H (matrixSiteVector β B v) (matrixSiteWeight Λ v) w hw
  rw [← matrixSiteVector_observables] at hz
  change hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
    (interpolationCoefficient n I 0))) 0 ≤ _ at hz
  rw [hc] at hz
  have htotal := hinter.trans (add_le_add hz le_rfl)
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ hNr).2
  dsimp only [X,H,c,n,m,I,F] at htotal ⊢
  nlinarith

end SK.Analytic

end
end

end OAI
