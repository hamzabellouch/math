import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixGuerraEndpoints
import OAI.Probability.SKBarriers.Replicas.MatrixGuerraOffset
import OAI.Probability.SKBarriers.Replicas.MatrixSKCovariance

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

variable {S : Type} [Fintype S] [Nonempty S]

def matrixSKLogPartition (N d : ℕ) (β : ℝ) (e : S → Fin N → Config d) (J : Disorder N) : ℝ :=
  Real.log (∑ s, Real.exp (β*∑ a, hamiltonian J (fun i => e s i a)))

theorem matrixSKLogPartition_continuous (N d : ℕ) (β : ℝ) (e : S → Fin N → Config d) :
    Continuous (matrixSKLogPartition N d β e) := by
  apply Continuous.log
    (continuous_finsetSum _ (fun s _ => Real.continuous_exp.comp
      (continuous_const.mul (continuous_finsetSum _ (fun a _ => continuous_hamiltonian (fun i => e s i a))))))
  intro J
  exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'

theorem matrixSKQuenched_endpoint (N d : ℕ) (β : ℝ) (e : S → Fin N → Config d) :
    (∫ z, affineLogPartition (fun _ : S => 0)
      (fun s => coordinateLinear (Fintype.card (Edge N)) (fun u => matrixSKObservables N d β e u s))
      z ∂fiberGaussian (Fintype.card (Edge N)) 0)=
        ∫ J, matrixSKLogPartition N d β e J ∂disorderLaw N := by
  simp only [affineLogPartition,matrixSKObservables_exponent,zero_add]
  change (∫ z, matrixSKLogPartition N d β e (enumeratedDisorder N z) ∂_)=_
  have H := enumeratedDisorder_measurePreserving N 0
  rw [← H.map_eq,integral_map H.measurable.aemeasurable (matrixSKLogPartition_continuous N d β e).aestronglyMeasurable]

theorem matrixSKGuerra {N d r k : ℕ} (hN : 0<N) (hr : 0<r) (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (e : S → Fin N → Config d) (he : Function.Injective e)
    (D Λ : Fin d → Fin d → ℝ)
    (hself : ∀ s, replicaCrossOverlap N d (fun i a => spin (e s i a)) (fun i a => spin (e s i a))=D)
    (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    (∫ J, matrixSKLogPartition N d β e J ∂disorderLaw N)/(N:ℝ) ≤
      vectorHierarchy ((k+1)*r) (siteBlockMass r k w) (matrixSiteVector β B (fun (a : Config d) u => spin (a u)))
        (siteValueTerminal (matrixSiteWeight Λ (fun (a : Config d) u => spin (a u)))) 0 - matrixInner d Λ D+
        (β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
          ∑ j, w j*matrixSquare d (factorPath d r k B j)) := by
  let v : Config d → Fin d → ℝ := fun a u => spin (a u)
  let X : S → Fin N → Fin d → ℝ := fun s i => v (e s i)
  let c : S → ℝ := fun s => ∑ i, matrixSiteWeight Λ v (e s i)
  let M:=Fintype.card (Edge N)
  let n:=blockDimension M (N*r) k
  let H:=matrixSKObservables N d β e
  let F:=matrixFieldObservables N d r k β B X
  let m:=weightedBlockMass M (N*r) k w
  let I:=blockInterpolationChoice M (N*r) k
  have hc : c=fun _ => (N:ℝ)*matrixInner d Λ D := by
    funext s
    rw [show c s=∑ i, matrixSiteWeight Λ v (e s i) from rfl,matrixSiteWeight_sum,hself s]
  have hinter := matrixFiniteInterpolation_offset hN hr β B X H (β^2*(d:ℝ)^2/2)
    (matrixSKObservables_covariance hN β e) D hself c w hw hs
  change hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
    (interpolationCoefficient n I 1))) 0 ≤ _ at hinter
  rw [hc,affineLogPartition_const_weight,hierarchyPressure_add_const n m
    (affineLogPartition_boundedDerivs (fun _ : S => 0) _) ((N:ℝ)*matrixInner d Λ D)] at hinter
  dsimp only at hinter
  rw [blockObservable_root_one,matrixSKQuenched_endpoint] at hinter
  have hz := siteBlock_root_zero_le hN e he H (matrixSiteVector β B v) (matrixSiteWeight Λ v) w hw
  rw [← matrixSiteVector_observables] at hz
  change hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
    (interpolationCoefficient n I 0))) 0 ≤ _ at hz
  rw [hc] at hz
  have htotal := hinter.trans (add_le_add hz le_rfl)
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ hNr).2
  dsimp only [X,H,c,n,m,I,F,M,v] at htotal ⊢
  nlinarith

def MatrixStates (N d : ℕ) (D : Fin d → Fin d → ℝ) :=
  {s : Fin N → Config d // replicaCrossOverlap N d (fun i a => spin (s i a)) (fun i a => spin (s i a))=D}

instance matrixStatesFintype (N d : ℕ) (D : Fin d → Fin d → ℝ) :
    Fintype (MatrixStates N d D) := by
  classical
  unfold MatrixStates
  infer_instance

def matrixConstrainedPressure (N d : ℕ) (β : ℝ) (D : Fin d → Fin d → ℝ) : ℝ :=
  (∫ J, Real.log (∑ s : MatrixStates N d D,
    Real.exp (β*∑ a, hamiltonian J (fun i => s.val i a))) ∂disorderLaw N)/(N:ℝ)

theorem matrixConstrainedPressure_le {N d r k : ℕ} (hN : 0<N) (hr : 0<r) (β : ℝ)
    (D Λ : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D))
    (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    matrixConstrainedPressure N d β D ≤
      vectorHierarchy ((k+1)*r) (siteBlockMass r k w) (matrixSiteVector β B (fun (a : Config d) u => spin (a u)))
        (siteValueTerminal (matrixSiteWeight Λ (fun (a : Config d) u => spin (a u)))) 0 - matrixInner d Λ D+
        (β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
          ∑ j, w j*matrixSquare d (factorPath d r k B j)) := by
  let := hD
  exact matrixSKGuerra hN hr β B (fun s : MatrixStates N d D => s.val) Subtype.val_injective
    D Λ (fun s => s.property) w hw hs

end SK.Analytic

end
end

end OAI
