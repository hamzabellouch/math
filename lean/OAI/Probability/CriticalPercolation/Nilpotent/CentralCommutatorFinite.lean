import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.CentralCommutatorQuotient

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G Q : Type*} [Group G] [Group Q]

theorem central_commutator_finite_of_quotient [Group.FG G] [Finite Q]
    (H : Subgroup G) (f : H →* Q) (hf : Surjective f)
    (hker : f.ker.map H.subtype≤Subgroup.center G)
    (hc : ⁅(⊤ : Subgroup G),H⁆≤Subgroup.center G) :
    ((⁅(⊤ : Subgroup G),H⁆ : Subgroup G) : Set G).Finite := by
  let C := ⁅(⊤ : Subgroup G),H⁆
  let _ : CommGroup C := {
    (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a.val) }
  let _ : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr
    (central_commutator_fg_of_quotient H f hf hker hc)
  have hpair (a : G) (b : H) : IsOfFinOrder (⁅a,(b:G)⁆) := by
    let t : H →* G := {
      toFun := fun b => ⁅a,(b:G)⁆
      map_one' := by simp
      map_mul' := by
        intro b d
        change ⁅a,(b:G)*(d:G)⁆=⁅a,(b:G)⁆*⁅a,(d:G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hd := hc (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
          (by trivial) d.property : ⁅a,(d:G)⁆∈C)
        calc
          ⁅a,(b:G)⁆*(b:G)*⁅a,(d:G)⁆*(b:G)⁻¹ =
            ⁅a,(b:G)⁆*((b:G)*⁅a,(d:G)⁆)*(b:G)⁻¹ := by group
          _ = ⁅a,(b:G)⁆*(⁅a,(d:G)⁆*(b:G))*(b:G)⁻¹ := by
            rw [Subgroup.mem_center_iff.mp hd (b:G)]
          _ = _ := by group }
    obtain ⟨m,hm,he⟩ := (isOfFinOrder_of_finite (f b)).exists_pow_eq_one
    have hb : b^m∈f.ker := by change f (b^m)=1; rwa [map_pow]
    have hz : ((b^m:H):G)∈Subgroup.center G := hker ⟨b^m,hb,rfl⟩
    have heq : t (b^m)=1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz a)
    rw [map_pow] at heq
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,heq⟩
  have ht : C≤(CommGroup.torsion C).map C.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a _ b hb
    let c : C := ⟨⁅a,b⁆,Subgroup.commutator_mem_commutator (by trivial) hb⟩
    refine ⟨c,?_,rfl⟩
    change IsOfFinOrder c
    obtain ⟨m,hm,he⟩ := (hpair a ⟨b,hb⟩).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,Subtype.ext he⟩
  let _ : Finite C := CommGroup.finite_of_fg_isMulTorsion C (fun c => by
    obtain ⟨d,hd,he⟩ := ht c.property
    have hcd : d=c := Subtype.ext he
    change IsOfFinOrder d at hd
    exact hcd ▸ hd)
  exact Set.toFinite _

end CriticalPercolation
end
end
end

end OAI
