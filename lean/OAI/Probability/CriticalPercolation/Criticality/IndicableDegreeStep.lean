import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.FiniteKernelNilpotent
import OAI.Probability.CriticalPercolation.Growth.KernelGrowthDescent
import OAI.Probability.CriticalPercolation.GraphGeometry.IntegerKernelGeneration
import OAI.Probability.CriticalPercolation.Nilpotent.GeneralNilpotentCore
import OAI.Probability.CriticalPercolation.LinearGroups.GeneralPeriodicCenter

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
universe u

theorem virtuallyNilpotent_of_indicability_degree_step
    (d : ℕ)
    (ih : ∀ (B : Type u) [Group B] [DecidableEq B],
      HasPolynomialDegree B d → Group.IsVirtuallyNilpotent B)
    (A : Type u) [Group A] [DecidableEq A]
    (hg : HasPolynomialDegree A (d+1))
    (hind : ∃ H : Subgroup A, H.FiniteIndex ∧
      ∃ f : H →* Multiplicative ℤ, Surjective f) :
    Group.IsVirtuallyNilpotent A := by
    rcases finite_or_infinite A with hfin | hinf
    · let _ := hfin
      exact virtuallyNilpotent_of_finite
    let _ := hinf
    obtain ⟨H,hHi,f,hf⟩ := hind
    let _ := hHi
    apply virtuallyNilpotent_of_finiteIndex H
    have hgH := hg.finiteIndex_subgroup H
    let _ : Group.FG H := hgH.fg
    let K := f.ker
    let _ : Group.FG K := hgH.integer_kernel_fg f hf
    let _ : Infinite (H ⧸ K) :=
      (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv.infinite_iff.mpr inferInstance
    have hgK := hgH.normal_subgroup_descent K
    have hvK := ih K hgK
    obtain ⟨P,hP,hPi,hPn⟩ := hgK.characteristic_nilpotent_core_general hvK
    let _ := hP
    let _ := hPi
    let _ := hPn
    let L := P.map K.subtype
    let e : P ≃* L := P.equivMapOfInjective K.subtype Subtype.val_injective
    let _ : L.Normal := characteristic_map_normal K P
    let _ : Group.IsNilpotent L := Group.nilpotent_of_surjective e.toMonoidHom e.surjective
    have hLK : L≤K := Subgroup.map_subtype_le P
    have he : L.subgroupOf K=P := by
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective P
    let _ : (L.subgroupOf K).FiniteIndex := he.symm ▸ hPi
    rcases finite_or_infinite L with hLf | hLi
    · let _ := hLf
      let _ : Finite P := Finite.of_equiv L e.symm.toEquiv
      let _ : Finite K := P.finite_iff_finite_and_finiteIndex.mpr ⟨inferInstance,hPi⟩
      exact CompactQuotient.virtuallyNilpotent_of_finite_kernel f (Set.toFinite _)
        (Group.IsNilpotent.isVirtuallyNilpotent inferInstance)
    · let _ := hLi
      let _ : Group.FG P := inferInstance
      let _ : Group.FG L := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
      obtain ⟨J,hJi,x,hx,hxinf⟩ := hgH.periodic_center_of_fg_nilpotent_kernel f hf L hLK
      let _ := hJi
      apply virtuallyNilpotent_of_finiteIndex J
      have hgJ := hgH.finiteIndex_subgroup J
      have hgQ := hgJ.quotient_descent (Subgroup.center J) x hx (orderOf_eq_zero hxinf)
      have hvQ := ih (J ⧸ Subgroup.center J) hgQ
      exact virtuallyNilpotent_of_central_kernel (QuotientGroup.mk' (Subgroup.center J))
        (by rw [QuotientGroup.ker_mk']) hvQ

end CriticalPercolation.SparseGrowth
end
end

end OAI
