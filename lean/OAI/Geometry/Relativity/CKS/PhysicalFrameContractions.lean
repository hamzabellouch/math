import OAI.Geometry.Relativity.CKS.PhysicalFrameTensor
import OAI.Geometry.Relativity.CKS.PhysicalFrameBasis

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma orthonormal_frame_gram {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    e.transpose*e=g⁻¹ := by
  apply (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc]
  exact orthonormal_frame_inverse ho

lemma orthonormal_frame_completeness {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) (i j : Fin 3) :
    (∑ a, e a i*e a j)=g⁻¹ i j := by
  exact congrFun (congrFun (orthonormal_frame_gram ho) i) j

lemma frame_tensor_matrix (k e : AmbientMat) :
    Matrix.of (fun i j => metricPair k (e i) (e j))=e*k*e.transpose := by
  ext i j
  change (∑ a, ∑ b, k a b*e i a*e j b) = (∑ b, (∑ a, e i a*k a b)*e j b)
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma frame_trace_exact (k : AmbientMat) {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (∑ i, metricPair k (e i) (e i))=(g⁻¹*k).trace := by
  change (Matrix.of (fun i j => metricPair k (e i) (e j))).trace = _
  rw [frame_tensor_matrix,Matrix.trace_mul_comm,
    ← Matrix.mul_assoc e.transpose e,orthonormal_frame_gram ho]

lemma symmetric_square_trace {k : AmbientMat} (hk : k.IsHermitian) :
    (∑ i, ∑ j, (k i j)^2)=(k*k).trace := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hermitian_real_symmetry hk i j]
  ring

lemma frame_tensor_norm_exact {k g e : AmbientMat} (hk : k.IsHermitian)
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (∑ i, ∑ j, (metricPair k (e i) (e j))^2)=(g⁻¹*k*g⁻¹*k).trace := by
  let t : AmbientMat := Matrix.of (fun i j => metricPair k (e i) (e j))
  have ht : t.IsHermitian := by
    ext i j
    change metricPair k (e j) (e i)=metricPair k (e i) (e j)
    exact metricPair_symm hk _ _
  change (∑ i, ∑ j, (t i j)^2)=_
  rw [symmetric_square_trace ht]
  have he : t=e*k*e.transpose := frame_tensor_matrix k e
  rw [he]
  calc
    _ = (e*(k*(e.transpose*e)*k*e.transpose)).trace := by congr 1; simp only [Matrix.mul_assoc]
    _ = ((k*(e.transpose*e)*k*e.transpose)*e).trace := Matrix.trace_mul_comm _ _
    _ = (k*(e.transpose*e)*k*(e.transpose*e)).trace := by congr 1; simp only [Matrix.mul_assoc]
    _ = (k*g⁻¹*k*g⁻¹).trace := by rw [orthonormal_frame_gram ho]
    _ = (g⁻¹*k*g⁻¹*k).trace := by
      rw [Matrix.trace_mul_comm (k*g⁻¹*k) g⁻¹]
      simp only [Matrix.mul_assoc]

theorem actualFrameEnergy_coordinate {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : (K x).IsHermitian) :
    actualFrameEnergy G K E x =
      (actualFrameScalar G E x+((G x)⁻¹*K x).trace^2-
        ((G x)⁻¹*K x*(G x)⁻¹*K x).trace)/2 := by
  have ho := h.2.2.2.2.1.self_of_nhds
  have ht := frame_trace_exact (K x) (e := Matrix.of (fun i j => E i x j)) ho
  have hn := frame_tensor_norm_exact hk (e := Matrix.of (fun i j => E i x j)) ho
  change (∑ i, metricPair (K x) (E i x) (E i x))=_ at ht
  change (∑ i, ∑ j, (metricPair (K x) (E i x) (E j x))^2)=_ at hn
  unfold actualFrameEnergy frameTensor
  rw [ht,hn]

end
end CKSAngularGeometry

end

end OAI
