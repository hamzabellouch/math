import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.VirtualIndicability
import OAI.Probability.CriticalPercolation.Nilpotent.FiniteKernelNilpotent
import OAI.Probability.CriticalPercolation.Growth.KernelGrowthDescent
import OAI.Probability.CriticalPercolation.LinearGroups.SolvablePeriodicCenter

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
universe u

theorem solvable_sparse_polynomial_virtuallyNilpotent (d : ℕ) :
    ∀ (A : Type u) [Group A] [DecidableEq A] [Group.IsSolvable A],
      HasPolynomialDegree A d → Group.IsVirtuallyNilpotent A := by
  induction d with
  | zero =>
    intro A _ _ _ hg
    let _ : Finite A := hg.finite
    exact virtuallyNilpotent_of_finite
  | succ d ih =>
    intro A _ _ _ hg
    rcases finite_or_infinite A with hfin | hinf
    · let _ := hfin
      exact virtuallyNilpotent_of_finite
    let _ := hinf
    obtain ⟨H,hHi,f,hf⟩ := hg.virtually_indicable
    let _ := hHi
    apply virtuallyNilpotent_of_finiteIndex H
    have hgH := hg.finiteIndex_subgroup H
    let _ : Group.FG H := hgH.fg
    let K := f.ker
    let _ : Group.FG K := hgH.solvable_subgroup_fg K
    let _ : Infinite (H ⧸ K) :=
      (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv.infinite_iff.mpr inferInstance
    have hgK := hgH.normal_subgroup_descent K
    have hvK := ih K hgK
    obtain ⟨P,hP,hPi,hPn⟩ := hgK.characteristic_nilpotent_core hvK
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
      obtain ⟨J,hJi,x,hx,hxinf⟩ := hgH.periodic_center_of_nilpotent_kernel f hf L hLK
      let _ := hJi
      apply virtuallyNilpotent_of_finiteIndex J
      have hgJ := hgH.finiteIndex_subgroup J
      have hgQ := hgJ.quotient_descent (Subgroup.center J) x hx (orderOf_eq_zero hxinf)
      have hvQ := ih (J ⧸ Subgroup.center J) hgQ
      exact virtuallyNilpotent_of_central_kernel (QuotientGroup.mk' (Subgroup.center J))
        (by rw [QuotientGroup.ker_mk']) hvQ

theorem HasPolynomialDegree.virtuallyNilpotent_of_solvable_finiteIndex
    {A : Type u} [Group A] [DecidableEq A] {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.FiniteIndex]
    [Group.IsSolvable H] : Group.IsVirtuallyNilpotent A := by
  exact virtuallyNilpotent_of_finiteIndex H
    (solvable_sparse_polynomial_virtuallyNilpotent d H (hg.finiteIndex_subgroup H))

end CriticalPercolation.SparseGrowth
end
end

end OAI
