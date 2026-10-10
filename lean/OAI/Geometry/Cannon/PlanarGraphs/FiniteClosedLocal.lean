import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonVertexLinks
open Set Metric Topology

lemma finite_closed_local {J X : Type*} [Finite J] [MetricSpace X]
    (C : J → Set X) (hC : ∀ j,IsClosed (C j)) (q : X) :
    ∃ r>0,∀ z∈ball q r,∀ j,z∈C j → q∈C j := by
  classical
  let U := ⋃ j : {j : J | q∉C j},C j.val
  have hU : IsClosed U := isClosed_iUnion_of_finite fun j=>hC j.val
  have hq : q∈Uᶜ := by
    rintro ⟨S,⟨j,rfl⟩,hq⟩
    exact j.property hq
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU.isOpen_compl q hq
  refine ⟨r,hr,?_⟩
  intro z hz j hj
  by_contra hn
  exact hsub hz (mem_iUnion.mpr ⟨⟨j,hn⟩,hj⟩)
lemma finite_pos_lower {J : Type*} [Finite J] (f : J → ℝ) (hf : ∀ j,0<f j) :
    ∃ r>0,∀ j,r<f j := by
  have ho : IsOpen (⋂j,Iio (f j)) := isOpen_iInter_of_finite fun _=>isOpen_Iio
  have hzero : (0:ℝ)∈⋂j,Iio (f j) := mem_iInter.mpr hf
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp ho 0 hzero
  refine ⟨ε/2,half_pos hε,mem_iInter.mp (hsub ?_)⟩
  rw [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos (half_pos hε)]
  linarith
end CannonVertexLinks

end
end
end
end

end OAI
