import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.NormalClosureGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma integer_kernel_normalClosure (S : Finset A)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (f : A →* Multiplicative ℤ) (a : A) (ha : f a=Multiplicative.ofAdd 1) :
    f.ker=Subgroup.normalClosure
      ((S.image (fun s => s*a^(-Multiplicative.toAdd (f s)))) : Set A) := by
  let F := S.image (fun s => s*a^(-Multiplicative.toAdd (f s)))
  let N := Subgroup.normalClosure (F : Set A)
  have hN : N≤f.ker := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hy
    change f (s*a^(-Multiplicative.toAdd (f s)))=1
    rw [map_mul,map_zpow,ha]
    apply Multiplicative.toAdd.injective
    simp
  let q := QuotientGroup.mk' N
  have hqa : ∀ x : A, q x=(q a)^Multiplicative.toAdd (f x) := by
    intro x
    have hx : x∈Subgroup.closure (S : Set A) := hgen.symm ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hm : x*a^(-Multiplicative.toAdd (f x))∈N :=
        Subgroup.subset_normalClosure (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      have he := (QuotientGroup.eq_one_iff _).mpr hm
      change q (x*a^(-Multiplicative.toAdd (f x)))=1 at he
      rw [map_mul,map_zpow,zpow_neg] at he
      exact mul_inv_eq_one.mp he
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul,hx,hy,←zpow_add,map_mul,toAdd_mul]
    | inv x _ hx =>
      rw [map_inv,hx,map_inv,toAdd_inv,zpow_neg]
  apply le_antisymm _ hN
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  change q x=1
  rw [hqa,MonoidHom.mem_ker.mp hx]
  simp

theorem HasPolynomialDegree.integer_kernel_fg {d : ℕ}
    (hg : HasPolynomialDegree A d) (f : A →* Multiplicative ℤ) (hf : Surjective f) :
    Group.FG f.ker := by
  obtain ⟨S,h1,hs,hgen,hS⟩ := (hasPolynomialDegree_iff d).mp hg
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  rw [integer_kernel_normalClosure S hgen f a ha]
  exact (Group.fg_iff_subgroup_fg _).mpr
    (normalClosure_fg_of_sparse_growth S _ h1 hs hgen d hS)

end CriticalPercolation.SparseGrowth
end
end

end OAI
