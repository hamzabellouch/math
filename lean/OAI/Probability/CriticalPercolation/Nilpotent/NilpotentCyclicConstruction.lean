import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.LowerCentralFG
import OAI.Probability.CriticalPercolation.Nilpotent.FGExtensions
import OAI.Probability.CriticalPercolation.Nilpotent.FiniteCyclicConstruction

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem nilpotent_subgroup_finite_cyclic_construction (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] (J : Subgroup G) : ∃ k, FiniteCyclicConstruction J k := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => J ⊓ (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : ∃ k, FiniteCyclicConstruction (L (n+1)) k) :
      ∃ k, FiniteCyclicConstruction (L n) k := by
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
    obtain ⟨k,hk⟩ := hn
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
    have hker := hk.of_equiv e.symm
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    have hker' : FiniteCyclicConstruction f.rangeRestrict.ker k := he.symm ▸ hker
    obtain ⟨m,hm⟩ := abelian_finite_cyclic_construction f.range
    exact ⟨k+m,FiniteCyclicConstruction.extension f.rangeRestrict
      f.rangeRestrict_surjective hker' hm⟩
  have base : ∃ k, FiniteCyclicConstruction (L c) k := by
    have he : L c=⊥ := by simp [L,hc]
    rw [he]
    exact ⟨0,.finite _⟩
  have hall : ∀ k, ∃ m, FiniteCyclicConstruction (L (c-k)) m := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k<c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · have he : c-k=c-(k+1) := by omega
        exact he ▸ ih
  have h := hall c
  have he : L (c-c)=J := by simp [L]
  exact he ▸ h

theorem nilpotent_finite_cyclic_construction (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] : ∃ k, FiniteCyclicConstruction G k := by
  obtain ⟨k,hk⟩ := nilpotent_subgroup_finite_cyclic_construction G ⊤
  exact ⟨k,hk.of_equiv Subgroup.topEquiv.symm⟩

end CriticalPercolation
end
end
end

end OAI
