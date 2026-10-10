import OAI.Geometry.Relativity.CKS.PhysicalConnectionRegularity
import OAI.Geometry.Relativity.CKS.PhysicalMomentumCovector

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma covariant_second_pair {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0)
    (i j k l : Fin 3) :
    metricPair (G x)
      (covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x)
      (E l x) = D (E i x) (fun y => frameCoefficient G E y j k l) x +
      ∑ m, frameCoefficient G E x j k m*frameCoefficient G E x i m l := by
  have hh := covariantVector_metric (hg.differentiableAt (by simp))
    ((covariantVector_contDiffAt hg (ne_of_gt hp.det_pos) (he j) (he k)).differentiableAt (by simp))
    ((he l).differentiableAt (by simp)) hp hs (E i x)
  have hpairs := metricPair_frame_right (G x) ho.self_of_nhds
    (covariantVector G (E i x) (E l) x) (covariantVector G (E j x) (E k) x)
  change (∑ m, frameCoefficient G E x i l m*frameCoefficient G E x j k m) = _ at hpairs
  have hm (m) := frameCoefficient_metric (hg.differentiableAt (by simp))
    (fun a => (he a).differentiableAt (by simp)) hp hs ho i l m
  simp_rw [hm] at hpairs
  have hpairs' : metricPair (G x) (covariantVector G (E j x) (E k) x)
      (covariantVector G (E i x) (E l) x) =
      -(∑ m, frameCoefficient G E x j k m*frameCoefficient G E x i m l) := by
    rw [← hpairs]
    simp only [neg_mul,Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  change D (E i x) (fun y => frameCoefficient G E y j k l) x = _ at hh
  rw [hpairs'] at hh
  linarith

def covariantDirectionLinear (G : PhysicalPoint → AmbientMat)
    (W : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) :
    PhysicalPoint →ₗ[ℝ] PhysicalPoint where
  toFun e := covariantVector G e W x
  map_add' e f := by
    ext k
    simp only [covariantVector,D,map_add,Pi.add_apply,
      add_mul,Finset.sum_add_distrib]
    ring
  map_smul' r e := by
    ext k
    simp only [covariantVector,D,map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma metricPair_sum_left (g : AmbientMat) (v : Fin 3 → PhysicalPoint) (w : PhysicalPoint) :
    metricPair g (∑ i, v i) w=∑ i, metricPair g (v i) w := by
  simp only [Fin.sum_univ_three,metricPair_add_left]

lemma covariant_frame_direction {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (ho : ∀ i j,
      metricPair (G x) (E i x) (E j x)=if i=j then 1 else 0)
    (e : PhysicalPoint) (j k : Fin 3) :
    metricPair (G x) (covariantVector G e (E j) x) (E k x)=
      ∑ m, metricPair (G x) e (E m x)*frameCoefficient G E x m j k := by
  have hex : e=∑ m, metricPair (G x) e (E m x) • E m x := by
    ext a
    simpa only [Fin.sum_univ_three,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
      (orthonormal_frame_expansion ho e a).symm
  change metricPair (G x) (covariantDirectionLinear G (E j) x e) (E k x)=_
  conv_lhs => rw [hex]
  rw [map_sum]
  simp only [map_smul,metricPair_sum_left,metricPair_smul_left]
  rfl

theorem actualFrameCurvature_operator {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0)
    (i j k l : Fin 3) :
    actualFrameCurvature G E x i j k l =
      metricPair (G x)
        (covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x) (E l x) -
      metricPair (G x)
        (covariantVector G (E j x) (fun y => covariantVector G (E i y) (E k) y) x) (E l x) -
      metricPair (G x) (covariantVector G (actualFrameBracket E x i j) (E k) x) (E l x) := by
  rw [covariant_second_pair hg he hp hs ho,covariant_second_pair hg he hp hs ho,
    covariant_frame_direction ho.self_of_nhds]
  simp only [actualFrameCurvature,frameBracketCoefficient,Finset.sum_sub_distrib]
  ring

lemma metricPair_sub_left (g : AmbientMat) (v w z : PhysicalPoint) :
    metricPair g (v-w) z=metricPair g v z-metricPair g w z := by
  simp only [metricPair,Pi.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

def curvatureVector (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : PhysicalPoint :=
  covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x -
  covariantVector G (E j x) (fun y => covariantVector G (E i y) (E k) y) x -
  covariantVector G (actualFrameBracket E x i j) (E k) x

theorem actualScalar_curvature_trace {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    actualFrameScalar G E x =
      ∑ i, ∑ j, metricPair (G x) (curvatureVector G E x i j j) (E i x) := by
  simp only [actualFrameScalar,curvatureVector,metricPair_sub_left]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact actualFrameCurvature_operator hg he hp hs ho i j j i

end
end CKSAngularGeometry

end

end OAI
