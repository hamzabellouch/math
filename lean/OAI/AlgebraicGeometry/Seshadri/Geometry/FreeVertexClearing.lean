import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.FreeVertices

namespace OAI


                                            
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

lemma freeVertex_cross_clearing {ι : Type*} [Fintype ι] (d : ℤ) (i j : Fin 3)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeVertex ι d j) :
    ∃ q : ℕ, T (K := K) (q • (weight j - weight i)) • m ∈ freeVertex ι d i := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨3*n+d.natAbs,fun a ha => ?_⟩
  apply supported_monomial_mul ((m a).coeff.support : Set (ℤ × ℤ)) (twistCone d i)
    ((3*n+d.natAbs) • (weight j-weight i)) _ (m a)
    (supported_of_support (m a) _ (fun w hw => hw))
  intro w hw
  have hbound := hn a w hw
  have hd0 := abs_nonneg d
  have hd1 := neg_abs_le d
  have hd2 := le_abs_self d
  have hj : w ∈ twistCone d j := (Finsupp.mem_supported K (m a).coeff).mp (hm a ha) hw
  fin_cases i <;> fin_cases j <;>
    simp [twistCone,vertexCone,weight,coneA,coneB,coneC] at hj ⊢ <;> omega

lemma freeA_vertex_clearing {ι : Type*} [Fintype ι] (d : ℤ)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeA ι) :
    ∃ q : ℕ, T (K := K) (q • (weight 1-weight 0)) • m ∈ freeVertex ι d 0 := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun a ha => ?_⟩
  apply supported_monomial_mul ((m a).coeff.support : Set (ℤ × ℤ)) (twistCone d 0)
    (n • (weight 1-weight 0)) _ (m a) (supported_of_support (m a) _ (fun w hw => hw))
  intro w hw
  have hb := hn a w hw
  have hj : w ∈ coneA := (Finsupp.mem_supported K (m a).coeff).mp (hm a ha) hw
  simp [twistCone,vertexCone,weight,coneA,coneB] at hj ⊢
  omega

lemma freeB_vertex_clearing {ι : Type*} [Fintype ι] (d : ℤ)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeB ι) :
    ∃ q : ℕ, T (K := K) (q • (weight 2-weight 0)) • m ∈ freeVertex ι d 0 := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun a ha => ?_⟩
  apply supported_monomial_mul ((m a).coeff.support : Set (ℤ × ℤ)) (twistCone d 0)
    (n • (weight 2-weight 0)) _ (m a) (supported_of_support (m a) _ (fun w hw => hw))
  intro w hw
  have hb := hn a w hw
  have hj : w ∈ coneB := (Finsupp.mem_supported K (m a).coeff).mp (hm a ha) hw
  simp [twistCone,vertexCone,weight,coneA,coneB] at hj ⊢
  omega

lemma freeC_vertex_clearing {ι : Type*} [Fintype ι] (d : ℤ)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeC ι d) :
    ∃ q : ℕ, T (K := K) (q • (weight 2-weight 1)) • m ∈ freeVertex ι d 1 := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun a ha => ?_⟩
  apply supported_monomial_mul ((m a).coeff.support : Set (ℤ × ℤ)) (twistCone d 1)
    (n • (weight 2-weight 1)) _ (m a) (supported_of_support (m a) _ (fun w hw => hw))
  intro w hw
  have hb := hn a w hw
  have hj : w ∈ coneC d := (Finsupp.mem_supported K (m a).coeff).mp (hm a ha) hw
  simp [twistCone,vertexCone,weight,coneA,coneC] at hj ⊢
  omega

end
end MaximalSeshadri.PlaneCech

end



end OAI
