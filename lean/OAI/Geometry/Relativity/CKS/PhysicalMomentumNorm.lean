import OAI.Geometry.Relativity.CKS.PhysicalFrameContractions
import OAI.Geometry.Relativity.CKS.PhysicalLeafTrace

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma covector_frame_square (ρ : PhysicalPoint) {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (∑ a, (∑ i, ρ i*e a i)^2)=metricPair g⁻¹ ρ ρ := by
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  unfold metricPair
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (∑ a, e a i*e a j)*ρ i*ρ j := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [orthonormal_frame_completeness ho]

lemma angular_covector_frame_square (ρ : Point) {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) :
    (∑ a, (∑ i, ρ i*angularFrame U γ s a i)^2)=
      ∑ i, ∑ j, γ⁻¹ i j*ρ i*ρ j := by
  have hc (i j) : (∑ a, angularFrame U γ s a i*angularFrame U γ s a j)=γ⁻¹ i j :=
    congrFun (congrFun (angularFrame_gram (s := s) hU hγ) i) j
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (∑ a, angularFrame U γ s a i*angularFrame U γ s a j)*ρ i*ρ j := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [hc]

theorem physical_covector_norm {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) (ρ : PhysicalPoint) :
    metricPair (foliationMetric U γ s)⁻¹ ρ ρ =
      (∑ i, ρ i*foliationNormal U s i)^2+
        ∑ i : Fin 2, ∑ j : Fin 2, γ⁻¹ i j*ρ i.succ*ρ j.succ := by
  rw [← covector_frame_square ρ (adaptedFrame_orthonormal hU hγ s),Fin.sum_univ_succ]
  rw [adaptedFrame_first]
  congr 1
  have ht (a : Fin 2) : (∑ i : Fin 3, ρ i*adaptedFrame U γ s a.succ i)=
      ∑ i : Fin 2, ρ i.succ*angularFrame U γ s a i := by
    rw [Fin.sum_univ_succ,adaptedFrame_radial,mul_zero,zero_add]
    rfl
  simp_rw [ht]
  exact angular_covector_frame_square (fun i => ρ i.succ) hU hγ

end
end CKSAngularGeometry

end

end OAI
