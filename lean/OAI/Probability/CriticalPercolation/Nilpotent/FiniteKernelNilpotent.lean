import Mathlib

namespace OAI

section
noncomputable section
open Set Function

namespace CriticalPercolation.CompactQuotient
variable {A B : Type*} [Group A] [Group B]

theorem virtuallyNilpotent_of_finite_kernel (f : A →* B)
    (hfin : (f.ker : Set A).Finite) (hB : Group.IsVirtuallyNilpotent B) :
    Group.IsVirtuallyNilpotent A := by
  let _ : Finite f.ker := hfin.to_subtype
  obtain ⟨N,hN,hNi⟩ := hB
  let _ := hN
  let _ := hNi
  let c : A →* MulAut f.ker := MulAut.conjNormal
  let P := N.comap f ⊓ c.ker
  let _ : c.ker.FiniteIndex := inferInstance
  let _ : (N.comap f).FiniteIndex := by
    constructor
    rw [N.index_comap]
    exact (inferInstance : (N.subgroupOf f.range).FiniteIndex).index_ne_zero
  let _ : P.FiniteIndex := inferInstance
  let j : P →* N :=
    { toFun := fun a => ⟨f a.val,a.property.1⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.val b.val) }
  have hker : j.ker≤Subgroup.center P := by
    intro a ha
    have haf : (a : A)∈f.ker := by
      exact congrArg Subtype.val ha
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    have hb : c b.val=1 := b.property.2
    have he := congrArg (fun e : MulAut f.ker => (e ⟨a.val,haf⟩).val) hb
    change b.val*a.val*b.val⁻¹=a.val at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  exact ⟨P,Subgroup.isNilpotent_of_ker_le_center j hker,inferInstance⟩

end CriticalPercolation.CompactQuotient
end
end

end OAI
