import OAI.Geometry.Relativity.CKS.PhysicalFrameCalculus

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma orthonormal_frame_inverse {g : AmbientMat} {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (g*(Matrix.transpose e))*e=1 := by
  have hh : e*(g*Matrix.transpose e)=1 := by
    ext i j
    change (∑ k, e i k * ∑ l, g k l*e j l) = if i=j then 1 else 0
    rw [← ho i j]
    simp only [metricPair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  exact mul_eq_one_comm.mp hh

lemma orthonormal_frame_expansion {g : AmbientMat} {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0)
    (v : PhysicalPoint) (j : Fin 3) :
    ∑ a, metricPair g v (e a)*e a j=v j := by
  have hm := orthonormal_frame_inverse ho
  calc
    _ = ∑ k, v k*((g*Matrix.transpose e)*e) k j := by
      simp only [metricPair, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ k, v k*(if k=j then 1 else 0) := by rw [hm]; rfl
    _ = v j := by simp

lemma metricPair_frame_left (k : AmbientMat) {g : AmbientMat}
    {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0)
    (v w : PhysicalPoint) :
    ∑ a, metricPair g v (e a)*metricPair k (e a) w=metricPair k v w := by
  calc
    _ = ∑ i, ∑ j, k i j*(∑ a, metricPair g v (e a)*e a i)*w j := by
      simp only [metricPair, Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = metricPair k v w := by simp_rw [orthonormal_frame_expansion ho]; rfl

lemma metricPair_frame_right (k : AmbientMat) {g : AmbientMat}
    {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0)
    (v w : PhysicalPoint) :
    ∑ a, metricPair g v (e a)*metricPair k w (e a)=metricPair k w v := by
  calc
    _ = ∑ i, ∑ j, k i j*w i*(∑ a, metricPair g v (e a)*e a j) := by
      simp only [metricPair, Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = metricPair k w v := by simp_rw [orthonormal_frame_expansion ho]; rfl

end
end CKSAngularGeometry

end

end OAI
