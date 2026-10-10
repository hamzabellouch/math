import OAI.Geometry.Relativity.CKS.PhysicalMomentumCoordinate
import OAI.Geometry.Relativity.CKS.PhysicalMomentumNorm

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma metricPair_smul_left (g : AmbientMat) (r : ℝ) (v w : PhysicalPoint) :
    metricPair g (r • v) w=r*metricPair g v w := by
  simp only [metricPair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_smul_right (g : AmbientMat) (r : ℝ) (v w : PhysicalPoint) :
    metricPair g v (r • w)=r*metricPair g v w := by
  simp only [metricPair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coordinateConnectionVector_add_right (G : PhysicalPoint → AmbientMat)
    (x e v w : PhysicalPoint) :
    coordinateConnectionVector G e (v+w) x=
      coordinateConnectionVector G e v x+coordinateConnectionVector G e w x := by
  ext k
  simp only [coordinateConnectionVector,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

lemma coordinateConnectionVector_smul_right (G : PhysicalPoint → AmbientMat)
    (x e v : PhysicalPoint) (r : ℝ) :
    coordinateConnectionVector G e (r • v) x=r • coordinateConnectionVector G e v x := by
  ext k
  simp only [coordinateConnectionVector,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def coordinateTensorCovariantLast (G K : PhysicalPoint → AmbientMat)
    (x e v : PhysicalPoint) : PhysicalPoint →ₗ[ℝ] ℝ where
  toFun := fun w => coordinateTensorCovariant G K e v w x
  map_add' := by
    intro w z
    simp only [coordinateTensorCovariant,coordinateConnectionVector_add_right,
      metricPair_add_right]
    erw [metricPair_add_right]
    ring
  map_smul' := by
    intro r w
    simp only [coordinateTensorCovariant,coordinateConnectionVector_smul_right,
      metricPair_smul_right,smul_eq_mul,RingHom.id_apply]
    erw [metricPair_smul_right]
    ring

def coordinateMomentumLinear (G K : PhysicalPoint → AmbientMat)
    (x : PhysicalPoint) : PhysicalPoint →ₗ[ℝ] ℝ where
  toFun := coordinateMomentum G K x
  map_add' := by
    intro w z
    have hc (i j) : coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) (w+z) x=
        coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x+
        coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) z x :=
      (coordinateTensorCovariantLast G K x _ _).map_add w z
    simp only [coordinateMomentum,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.of_apply,hc,mul_add,Finset.sum_add_distrib,D,map_add]
    ring
  map_smul' := by
    intro r w
    have hc (i j) : coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) (r • w) x=
        r*coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x :=
      (coordinateTensorCovariantLast G K x _ _).map_smul r w
    simp only [coordinateMomentum,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.of_apply,hc,D,map_smul,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm _ r,← Finset.mul_sum]
    ring

lemma coordinateMomentum_expansion (G K : PhysicalPoint → AmbientMat)
    (x w : PhysicalPoint) :
    coordinateMomentum G K x w=
      ∑ i, coordinateMomentum G K x (CKSRealizedRound.basis i)*w i := by
  change coordinateMomentumLinear G K x w=_
  conv_lhs => rw [direction_expansion w]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul,coordinateMomentumLinear,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  ring

def momentumCovector (G K : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : PhysicalPoint :=
  fun i => coordinateMomentum G K x (CKSRealizedRound.basis i)

theorem physical_momentum_frame_norm {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : DifferentiableAt ℝ K x) :
    (∑ a, (actualFrameMomentum G K E x a)^2)=
      metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) := by
  conv_lhs => arg 2; ext a; rw [actualFrameMomentum_coordinate h hk,coordinateMomentum_expansion]
  exact covector_frame_square (momentumCovector G K x)
    (e := Matrix.of (fun i j => E i x j)) h.2.2.2.2.1.self_of_nhds

theorem physical_momentum_normal_tangential {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) (G K : PhysicalPoint → AmbientMat) (x : PhysicalPoint) :
    metricPair (foliationMetric U γ s)⁻¹ (momentumCovector G K x) (momentumCovector G K x)=
      (coordinateMomentum G K x (foliationNormal U s))^2+
        ∑ i : Fin 2, ∑ j : Fin 2,
          γ⁻¹ i j*momentumCovector G K x i.succ*momentumCovector G K x j.succ := by
  rw [physical_covector_norm hU hγ]
  congr 1
  rw [coordinateMomentum_expansion]
  rfl

end
end CKSAngularGeometry

end

end OAI
