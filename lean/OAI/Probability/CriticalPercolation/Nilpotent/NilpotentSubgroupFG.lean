import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.LowerCentralFG
import OAI.Probability.CriticalPercolation.Nilpotent.FGExtensions

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem nilpotent_subgroup_fg (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] (J : Subgroup G) : Group.FG J := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => J ⊓ (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : Group.FG (L (n+1))) : Group.FG (L n) := by
    let F := lowerFactor G n
    let _ : CommGroup F := {
      (inferInstance : Group F) with
      mul_comm := fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp (lowerFactor_central G n b.property) a.val) }
    let _ : Group.FG F := lowerFactor_fg G n
    let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property.2,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    let _ : Group.FG f.range := abelian_subgroup_fg f.range
    let _ : Group.FG (L (n+1)) := hn
    have hemem (x : L n) : x∈f.ker ↔ x.val∈(⊤ : Subgroup G).lowerCentralSeries (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃* f.ker := {
      toFun := fun x => ⟨⟨x.val,⟨x.property.1,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property.2⟩⟩,
        (hemem _).mpr x.property.2⟩
      invFun := fun x => ⟨x.val.val,⟨x.val.property.1,(hemem _).mp x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intros; rfl }
    let _ : Group.FG f.ker := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    let _ : Group.FG f.rangeRestrict.ker := he.symm ▸ (inferInstance : Group.FG f.ker)
    exact fg_of_kernel_quotient f.rangeRestrict f.rangeRestrict_surjective
  have base : Group.FG (L c) := by
    have he : L c=⊥ := by simp [L,hc]
    rw [he]
    infer_instance
  have hall : ∀ k, Group.FG (L (c-k)) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k<c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · simpa [Nat.sub_eq_zero_of_le (by omega : c≤k),
          Nat.sub_eq_zero_of_le (by omega : c≤k+1)] using ih
  have h := hall c
  simpa [L] using h

end CriticalPercolation
end
end
end

end OAI
