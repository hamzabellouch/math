import OAI.Geometry.Relativity.CKS.PhysicalFrameConnection
import OAI.Geometry.Relativity.CKS.FoliationOrthonormalFrame

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma coordinateCovariantNormal_direction (G : PhysicalPoint → AmbientMat)
    (N : PhysicalPoint → PhysicalPoint) (x e : PhysicalPoint) (k : Fin 3) :
    covariantVector G e N x k = ∑ i, e i*coordinateCovariantNormal G N x i k := by
  rw [covariantVector,D_direction_expansion]
  simp only [coordinateCovariantNormal,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma normalCovariant_frame {G : PhysicalPoint → AmbientMat}
    (N : PhysicalPoint → PhysicalPoint) {x : PhysicalPoint} (hg : (G x).PosDef)
    (e v : PhysicalPoint) :
    metricPair (G x) (covariantVector G e N x) v =
      metricPair (coordinateNormalCovariant G N x) e v := by
  unfold metricPair
  simp_rw [coordinateCovariantNormal_direction]
  simp only [Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ i, ∑ j, (∑ l, coordinateCovariantNormal G N x i l*G x l j)*e i*v j := by
      simp only [Finset.sum_mul]
      conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by simp_rw [coordinateNormalCovariant_is_LeviCivita hg]

lemma metricPair_tangential_slots (k : AmbientMat) (e v : PhysicalPoint)
    (he : e 0=0) (hv : v 0=0) :
    metricPair k e v = ∑ a : Fin 2, ∑ b : Fin 2, k a.succ b.succ*e a.succ*v b.succ := by
  simp only [metricPair,Fin.sum_univ_succ,he,hv,mul_zero,zero_mul,Finset.sum_const_zero,zero_add]

def sourceChi (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) : Mat := fun a b =>
  U x/2 * (D (CKSRealizedRound.basis 0) (fun y => γ y a b) x -
    ∑ c, (s x c*D (CKSRealizedRound.basis c.succ) (fun y => γ y a b) x +
      γ x c b*D (CKSRealizedRound.basis a.succ) (fun y => s y c) x +
      γ x a c*D (CKSRealizedRound.basis b.succ) (fun y => s y c) x))

theorem leaf_frame_chi {U : PhysicalPoint → ℝ} {γ : PhysicalPoint → Mat}
    {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b : Fin 2) :
    frameCoefficient (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x a.succ 0 b.succ =
      ∑ i : Fin 2, ∑ j : Fin 2, sourceChi U γ s x i j *
        adaptedFrame (U x) (γ x) (s x) a.succ i.succ *
        adaptedFrame (U x) (γ x) (s x) b.succ j.succ := by
  unfold frameCoefficient
  change metricPair _ (covariantVector _ _ (fun y => foliationNormal (U y) (s y)) x) _ = _
  erw [normalCovariant_frame (G := fun y => foliationMetric (U y) (γ y) (s y))
    (fun y => foliationNormal (U y) (s y)) (foliationMetric_posDef h0.ne' hp.self_of_nhds (s x))]
  erw [metricPair_tangential_slots _ _ _ (adaptedFrame_radial _ _ _ a)
    (adaptedFrame_radial _ _ _ b)]
  have hχ := (physical_foliation_leaf_geometry hU hγ hs h0 hp).1
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hχ]; rfl))

theorem leaf_frame_acceleration {U : PhysicalPoint → ℝ} {γ : PhysicalPoint → Mat}
    {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a : Fin 2) :
    frameCoefficient (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x 0 0 a.succ =
      ∑ b : Fin 2, (D (CKSRealizedRound.basis b.succ) U x/U x)*
        adaptedFrame (U x) (γ x) (s x) a.succ b.succ := by
  unfold frameCoefficient
  change metricPair _ (covariantVector _ (foliationNormal (U x) (s x))
    (fun y => foliationNormal (U y) (s y)) x) _ = _
  erw [normalCovariant_frame (G := fun y => foliationMetric (U y) (γ y) (s y))
    (fun y => foliationNormal (U y) (s y)) (foliationMetric_posDef h0.ne' hp.self_of_nhds (s x))]
  unfold metricPair
  rw [Finset.sum_comm]
  rw [Fin.sum_univ_succ]
  simp only [adaptedFrame_radial,mul_zero,Finset.sum_const_zero,zero_add]
  have hB := (physical_foliation_leaf_geometry hU hγ hs h0 hp).2
  apply Finset.sum_congr rfl
  intro b _
  rw [← hB b,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end CKSAngularGeometry

end

end OAI
