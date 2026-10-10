import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.LowerCentralFinite

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem nilpotent_finite_of_finite_factors (G : Type*) [Group G]
    [Group.IsNilpotent G] (hfin : ∀ n, Finite (lowerFactor G n)) : Finite G := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : Finite (L (n+1))) : Finite (L n) := by
    let F := lowerFactor G n
    let _ : Finite F := hfin n
    let q := QuotientGroup.mk' (L (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hemem (x : L n) : x∈f.ker ↔ x.val∈L (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃ f.ker := {
      toFun := fun x => ⟨⟨x.val,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property⟩,
        (hemem _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val,(hemem _).mp x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
    let _ : Finite f.ker := Finite.of_equiv _ e
    exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance,inferInstance⟩
  have base : Finite (L c) := by
    change Finite ((⊤ : Subgroup G).lowerCentralSeries c)
    rw [hc]
    infer_instance
  have hall : ∀ k, Finite (L (c-k)) := by
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
  have h : Finite (⊤ : Subgroup G) := by simpa [L] using hall c
  let _ := h
  exact Finite.of_equiv _ (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv

theorem nilpotent_finite_of_finite_abelianization (G : Type*) [Group G]
    [Group.FG G] [Group.IsNilpotent G] [Finite (Abelianization G)] : Finite G := by
  have he : (⊤ : Subgroup G).lowerCentralSeries 1=commutator G :=
    Subgroup.top_lowerCentralSeries_one
  let _ : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1) := by
    rw [he]
    exact (inferInstance : Finite (Abelianization G))
  let _ : Finite (lowerFactor G 0) := inferInstance
  exact nilpotent_finite_of_finite_factors G (lowerFactor_finite G)

end CriticalPercolation
end
end
end

end OAI
