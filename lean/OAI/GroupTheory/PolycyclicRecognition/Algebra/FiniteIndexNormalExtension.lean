import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace OAI

/-! # Finite index from the kernel and quotient of a normal extension -/

noncomputable section
namespace PolycyclicRecognition

open scoped Pointwise
variable {G : Type*} [Group G]

theorem finiteIndex_of_normal_extension (N H : Subgroup G) [N.Normal]
    [(H.comap N.subtype).FiniteIndex]
    [(H.map (QuotientGroup.mk' N)).FiniteIndex] : H.FiniteIndex := by
  let P := H ⊔ N
  let J := H.subgroupOf P
  let L := H.comap N.subtype
  let f : (N ⧸ L) → (P ⧸ J) := Quotient.lift (s := QuotientGroup.leftRel L)
    (fun n : N => ((⟨(n : G), (show N ≤ P from le_sup_right) n.property⟩ : P) : P ⧸ J)) (by
      intro x y hxy
      apply QuotientGroup.eq.mpr
      change (x : G)⁻¹ * y ∈ H
      exact (QuotientGroup.leftRel_apply (s := L)).mp hxy)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    have hx : (x : G) ∈ (N : Set G) * (H : Set G) := by
      rw [← Subgroup.normal_mul, sup_comm]
      exact x.property
    obtain ⟨n, hn, h, hh, he⟩ := hx
    refine ⟨Quotient.mk'' (⟨n, hn⟩ : N), ?_⟩
    apply QuotientGroup.eq.mpr
    change n⁻¹ * (x : G) ∈ H
    rw [← he, inv_mul_cancel_left]
    exact hh
  let : Finite (P ⧸ J) := Finite.of_surjective f hf
  have hJ : J.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hP : P.FiniteIndex := by
    have he : (H.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = P := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← he]
    infer_instance
  refine ⟨?_⟩
  rw [← Subgroup.relIndex_mul_index (show H ≤ P from le_sup_left)]
  exact mul_ne_zero hJ.index_ne_zero hP.index_ne_zero

end PolycyclicRecognition

end

end OAI
