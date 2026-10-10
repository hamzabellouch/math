import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.NilpotentSubgroupFG
import OAI.Probability.CriticalPercolation.Nilpotent.AbelianConjugationGrowth
import OAI.Probability.CriticalPercolation.Nilpotent.NilpotentInfiniteCenter
import OAI.Probability.CriticalPercolation.Nilpotent.FiniteCyclicExtensionIndex

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma HasPolynomialDegree.periodic_center_of_fg_nilpotent_kernel {d : ℕ}
    (hg : HasPolynomialDegree A d)
    (f : A →* Multiplicative ℤ) (hf : Surjective f)
    (L : Subgroup A) [L.Normal] [Group.IsNilpotent L] [Group.FG L] [Infinite L]
    (hLK : L ≤ f.ker) [(L.subgroupOf f.ker).FiniteIndex] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ x : H,
      x∈Subgroup.center H ∧ ¬IsOfFinOrder x := by
  let Z := Subgroup.center L
  let _ : Infinite Z := infinite_center_of_nilpotent
  let C := Z.map L.subtype
  let e : Z ≃* C := Z.equivMapOfInjective L.subtype Subtype.val_injective
  let _ : C.Normal := characteristic_map_normal L Z
  let _ : IsMulCommutative C := ⟨⟨fun x y => e.symm.injective (by
    simp only [map_mul]; exact mul_comm _ _)⟩⟩
  let _ : Infinite C := Infinite.of_injective e e.injective
  let _ : Group.FG Z := nilpotent_subgroup_fg L Z
  let _ : Group.FG C := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  obtain ⟨m,hm,x,hx,hfix⟩ := hg.abelian_normal_periodic_direction C a
  let H := Subgroup.centralizer ({x.val} : Set A)
  have hLH : L≤H := by
    intro l hl
    obtain ⟨z,hz,hzx⟩ := x.property
    rw [Subgroup.mem_centralizer_singleton_iff,←hzx]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨l,hl⟩)
  have haH : a^m∈H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have he := congrArg Subtype.val hfix
    change a^m*x.val*(a^m)⁻¹=x.val at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hHi : H.FiniteIndex := finiteIndex_of_normal_kernel_subgroup f L hLK a ha H hLH m hm haH
  let y : H := ⟨x.val,by rw [Subgroup.mem_centralizer_singleton_iff]⟩
  refine ⟨H,hHi,y,?_,?_⟩
  · rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp w.property
  · intro hy
    obtain ⟨k,hk,he⟩ := hy.exists_pow_eq_one
    apply hx
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨k,hk,Subtype.ext (congrArg (fun z : H => z.val) he)⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
