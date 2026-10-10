import Mathlib

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem cyclic_infinite_subgroup_finiteIndex {G : Type*} [Group G]
    (e : G ≃* Multiplicative ℤ) (J : Subgroup G) [Infinite J] : J.FiniteIndex := by
  let a : Additive G ≃+ ℤ := e.toAdditive.trans (AddEquiv.additiveMultiplicative ℤ)
  let K := J.toAddSubgroup.map a.toAddMonoidHom
  obtain ⟨j,hj⟩ := exists_ne (1 : J)
  let z := a (Additive.ofMul j.val)
  have hz : z≠0 := by
    intro h
    have he : Additive.ofMul j.val=0 := a.injective (h.trans a.map_zero.symm)
    apply hj
    exact Subtype.ext he
  have hmem : z∈K := ⟨Additive.ofMul j.val,j.property,rfl⟩
  have hZ : (AddSubgroup.zmultiples z).FiniteIndex := by
    constructor
    rw [Int.index_zmultiples]
    exact Int.natAbs_ne_zero.mpr hz
  let _ := hZ
  have hK : K.FiniteIndex := AddSubgroup.finiteIndex_of_le (AddSubgroup.zmultiples_le.mpr hmem)
  constructor
  have hn := hK.index_ne_zero
  have he : K.index=J.index := by
    exact (AddSubgroup.index_map_equiv J.toAddSubgroup a).trans J.index_toAddSubgroup
  rwa [he] at hn

end CriticalPercolation
end
end
end

end OAI
