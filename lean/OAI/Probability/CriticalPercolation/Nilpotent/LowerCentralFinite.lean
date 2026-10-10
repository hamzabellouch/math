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
variable (G : Type*) [Group G]

theorem lowerFactor_finite [Group.FG G] [Finite (lowerFactor G 0)] (n : ℕ) :
    Finite (lowerFactor G n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
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
    let _ := ih
    have hfin := central_commutator_finite_of_quotient H f hf hker
      (hcomm ▸ lowerFactor_central G (n+1))
    rw [hcomm] at hfin
    exact hfin.to_subtype

end CriticalPercolation
end
end
end

end OAI
