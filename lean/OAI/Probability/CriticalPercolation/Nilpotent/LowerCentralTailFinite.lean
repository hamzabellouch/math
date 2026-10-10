import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.LowerCentralFG
import OAI.Probability.CriticalPercolation.Nilpotent.CentralCommutatorFinite

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation

lemma lowerFactor_finite_step (G : Type*) [Group G] [Group.FG G] (n : ℕ)
    [Finite (lowerFactor G n)] : Finite (lowerFactor G (n+1)) := by
  let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
  let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
  let π := QuotientGroup.mk' M
  let σ := QuotientGroup.mk' N
  have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
  let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
    rw [QuotientGroup.ker_mk']; exact hMN)
  have hq (g : G) : q (π g)=σ g := rfl
  let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
  let f : H →* lowerFactor G n := {
    toFun := fun h => ⟨q h.val,by
      obtain ⟨g,hg,he⟩ := h.property
      exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
    map_one' := by apply Subtype.ext; exact q.map_one
    map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
  have hf : Surjective f := by
    rintro ⟨x,g,hg,rfl⟩
    exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
  have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
    rintro x ⟨h,hh,rfl⟩
    obtain ⟨g,hg,he⟩ := h.property
    apply lowerFactor_central G (n+1)
    refine ⟨g,?_,he⟩
    have heq : σ g=1 := by
      rw [←hq,he]
      exact congrArg Subtype.val hh
    change g∈N
    rw [←QuotientGroup.ker_mk' N]
    exact heq
  have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
    have hπ : (⊤ : Subgroup G).map π=⊤ :=
      Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
    change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
      ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
    rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
      ←Subgroup.lowerCentralSeries_succ]
  have hfin := central_commutator_finite_of_quotient H f hf hker
    (hcomm ▸ lowerFactor_central G (n+1))
  rw [hcomm] at hfin
  exact hfin.to_subtype

theorem nilpotent_lower_finite_of_tail (G : Type*) [Group G]
    [Group.IsNilpotent G] (start : ℕ)
    (hfin : ∀ n, start≤n → Finite (lowerFactor G n)) :
    Finite ((⊤ : Subgroup G).lowerCentralSeries start) := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hsn : start≤n) (hn : Finite (L (n+1))) : Finite (L n) := by
    let F := lowerFactor G n
    let _ : Finite F := hfin n hsn
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

  have hall : ∀ k n, c≤n+k → start≤n → Finite (L n) := by
    intro k
    induction k with
    | zero =>
      intro n hcn _
      have hn : L n=⊥ := by
        apply le_antisymm ?_ bot_le
        calc
          L n ≤ L c := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
          _ = ⊥ := hc
      rw [hn]
      infer_instance
    | succ k ih =>
      intro n hcn hsn
      exact step n hsn (ih (n+1) (by omega) (by omega))
  exact hall c start (by omega) le_rfl

end CriticalPercolation
end
end
end

end OAI
