import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.CharacteristicNilpotentCore

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in
lemma virtuallyNilpotent_of_surjective (f : A →* B) (hf : Surjective f)
    (hv : Group.IsVirtuallyNilpotent A) : Group.IsVirtuallyNilpotent B := by
  obtain ⟨N,hN,hNi⟩ := hv
  let _ := hN
  let _ := hNi
  refine ⟨N.map f,?_,⟨fun he => hNi.index_ne_zero (by have hh := N.index_map_dvd hf; simpa [he] using hh)⟩⟩
  let g : N →* N.map f := {
    toFun := fun x => ⟨f x,⟨x,x.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val) }
  apply Group.nilpotent_of_surjective g
  rintro ⟨y,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

omit [DecidableEq B] in
lemma finite_of_torsion_virtuallyNilpotent_growth {d : ℕ}
    (hg : HasPolynomialDegree A d) (ht : IsMulTorsion A)
    (hv : Group.IsVirtuallyNilpotent A) : Finite A := by
  obtain ⟨N,hN,hNi⟩ := hv
  let _ := hN
  let _ := hNi
  let _ : Finite N := finite_of_torsion_solvable_sparse_growth
    (hg.finiteIndex_subgroup N) (ht.subgroup N)
  exact N.finite_iff_finite_and_finiteIndex.mpr ⟨inferInstance,hNi⟩

omit [DecidableEq B] in
lemma HasPolynomialDegree.powerSubgroup_finiteIndex {d : ℕ}
    (hg : HasPolynomialDegree A d) (hv : Group.IsVirtuallyNilpotent A)
    (k : ℕ) (hk : 0<k) : (powerSubgroup A k).FiniteIndex := by
  let P := powerSubgroup A k
  have ht : IsMulTorsion (A ⧸ P) := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective P q
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨k,hk,?_⟩
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_closure ⟨x,rfl⟩
  have hq := hg.of_surjective (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  have hvq := virtuallyNilpotent_of_surjective (QuotientGroup.mk' P)
    (QuotientGroup.mk'_surjective P) hv
  let _ : Finite (A ⧸ P) := finite_of_torsion_virtuallyNilpotent_growth hq ht hvq
  exact Subgroup.finiteIndex_of_finite_quotient

omit [DecidableEq B] in
lemma HasPolynomialDegree.characteristic_nilpotent_core_general {d : ℕ}
    (hg : HasPolynomialDegree A d) (hv : Group.IsVirtuallyNilpotent A) :
    ∃ P : Subgroup A, P.Characteristic ∧ P.FiniteIndex ∧ Group.IsNilpotent P := by
  obtain ⟨L,hL,hLi⟩ := hv
  let _ := hL
  let _ := hLi
  let N := L.normalCore
  let k := Nat.card (A ⧸ N)
  have hk : 0 < k := Nat.card_pos
  let P := powerSubgroup A k
  have hPL : P≤L := (powerSubgroup_le_finiteIndex N).trans L.normalCore_le
  refine ⟨P,inferInstance,hg.powerSubgroup_finiteIndex ⟨L,hL,hLi⟩ k hk,?_⟩
  let f : P →* L := Subgroup.inclusion hPL
  apply Subgroup.isNilpotent_of_ker_le_center f
  rw [(MonoidHom.ker_eq_bot_iff f).mpr (Subgroup.inclusion_injective hPL)]
  exact bot_le

end CriticalPercolation.SparseGrowth
end
end

end OAI
