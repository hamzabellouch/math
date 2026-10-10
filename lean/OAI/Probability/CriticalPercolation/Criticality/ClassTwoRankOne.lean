import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.CentralCommutatorGeneration

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G A : Type*} [Group G] [Group A]

def centralCommHom (hc : commutator G≤Subgroup.center G) (a : G) :
    G →* commutator G where
  toFun b := ⟨⁅a,b⁆,Subgroup.commutator_mem_commutator (by trivial) (by trivial)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' b d := by
    apply Subtype.ext
    change ⁅a,b*d⁆=⁅a,b⁆*⁅a,d⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hd := hc (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
      (H₂ := ⊤) (by trivial) (by trivial) : ⁅a,d⁆∈commutator G)
    calc
      ⁅a,b⁆*b*⁅a,d⁆*b⁻¹ = ⁅a,b⁆*(b*⁅a,d⁆)*b⁻¹ := by group
      _ = ⁅a,b⁆*(⁅a,d⁆*b)*b⁻¹ := by rw [Subgroup.mem_center_iff.mp hd b]
      _ = _ := by group

theorem class_two_commutator_finite_of_cyclic_mod_torsion [Group.FG G]
    (hc : commutator G≤Subgroup.center G) (ρ : G →* A)
    (hker : ρ.ker≤Subgroup.center G) (g : G)
    (hcyc : ∀ a : G, ∃ k : ℤ, IsOfFinOrder (ρ (a*g^(-k)))) :
    (commutator G : Set G).Finite := by
  let C := commutator G
  let _ : CommGroup C := {
    (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a.val) }
  let _ : Group.FG C := class_two_commutator_fg hc
  let t := centralCommHom hc
  have ht (a b : G) (hb : IsOfFinOrder (ρ b)) : IsOfFinOrder (t a b) := by
    obtain ⟨m,hm,he⟩ := hb.exists_pow_eq_one
    have hpow : b^m∈ρ.ker := by change ρ (b^m)=1; rwa [map_pow]
    have hz := hker hpow
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m,hm,?_⟩
    rw [←map_pow]
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz a)
  have hself : t g g=1 := by apply Subtype.ext; simp [t,centralCommHom,commutatorElement_def]
  have hga (a : G) : IsOfFinOrder (t g a) := by
    obtain ⟨k,hk⟩ := hcyc a
    have h := ht g (a*g^(-k)) hk
    simpa only [map_mul,map_zpow,hself,one_zpow,mul_one] using h
  have hag (a : G) : IsOfFinOrder (t a g) := by
    have he : t a g=(t g a)⁻¹ := by
      apply Subtype.ext
      exact (commutatorElement_inv g a).symm
    rw [he]
    exact (hga a).inv
  have hab (a b : G) : IsOfFinOrder (t a b) := by
    obtain ⟨k,hk⟩ := hcyc b
    have hw := ht a (b*g^(-k)) hk
    have hg : (t a g)^k∈CommGroup.torsion C :=
      (CommGroup.torsion C).zpow_mem (hag a) k
    have hh := (CommGroup.torsion C).mul_mem hw hg
    have he : t a (b*g^(-k))*(t a g)^k=t a b := by
      rw [map_mul,map_zpow,zpow_neg]
      group
    rw [he] at hh
    exact hh
  have hsub : C≤(CommGroup.torsion C).map C.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact ⟨t a b,hab a b,rfl⟩
  let _ : Finite C := CommGroup.finite_of_fg_isMulTorsion C (fun c => by
    obtain ⟨d,hd,he⟩ := hsub c.property
    change IsOfFinOrder d at hd
    exact (show d=c from Subtype.ext he) ▸ hd)
  exact Set.toFinite _

end CriticalPercolation
end
end
end

end OAI
