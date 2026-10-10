import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.LowerCentralTailFinite
import OAI.Probability.CriticalPercolation.Criticality.ClassTwoRankOne
import OAI.Probability.CriticalPercolation.Nilpotent.CyclicModTorsion

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation

theorem first_commutator_factor_finite (G : Type*) [Group G] [Group.FG G]
    (φ : Abelianization G →* Multiplicative ℤ) (hφ : Surjective φ)
    (hk : (φ.ker : Set (Abelianization G)).Finite) : Finite (lowerFactor G 1) := by
  let M := (⊤ : Subgroup G).lowerCentralSeries 2
  let p := QuotientGroup.mk' M
  have hM : M≤commutator G := by
    rw [←Subgroup.top_lowerCentralSeries_one]
    exact (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
  let ρ : (G ⧸ M) →* Abelianization G := QuotientGroup.lift M (Abelianization.of : G →* Abelianization G) (by
    rw [Abelianization.ker_of]; exact hM)
  have hρ : Surjective ρ := by
    intro a
    obtain ⟨g,rfl⟩ := (QuotientGroup.mk_surjective (s := commutator G)) a
    exact ⟨p g,rfl⟩
  have hcomm : commutator (G ⧸ M)=lowerFactor G 1 := by
    have hp : (⊤ : Subgroup G).map p=⊤ :=
      Subgroup.map_top_of_surjective p QuotientGroup.mk_surjective
    change ⁅⊤,⊤⁆=((⊤ : Subgroup G).lowerCentralSeries 1).map p
    rw [Subgroup.top_lowerCentralSeries_one,commutator,Subgroup.map_commutator,hp]
  have hc : commutator (G ⧸ M)≤Subgroup.center (G ⧸ M) := by
    rw [hcomm]
    exact lowerFactor_central G 1
  have hker : ρ.ker≤Subgroup.center (G ⧸ M) := by
    intro x hx
    obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g∈commutator G := by
      change Abelianization.of g=1 at hx
      exact (QuotientGroup.eq_one_iff g).mp hx
    apply lowerFactor_central G 1
    exact ⟨g,hg,rfl⟩
  obtain ⟨g,hg⟩ := cyclic_mod_torsion_of_finite_kernel ρ hρ φ hφ hk
  have hf := class_two_commutator_finite_of_cyclic_mod_torsion hc ρ hker g hg
  rw [hcomm] at hf
  exact hf.to_subtype

theorem nilpotent_commutator_finite_of_cyclic_abelianization (G : Type*)
    [Group G] [Group.FG G] [Group.IsNilpotent G]
    (φ : Abelianization G →* Multiplicative ℤ) (hφ : Surjective φ)
    (hk : (φ.ker : Set (Abelianization G)).Finite) :
    (commutator G : Set G).Finite := by
  have hfirst := first_commutator_factor_finite G φ hφ hk
  have htail : ∀ n, 1≤n → Finite (lowerFactor G n) := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => exact hfirst
    | succ n hn ih =>
      let _ := ih
      exact lowerFactor_finite_step G n
  have hf := nilpotent_lower_finite_of_tail G 1 htail
  rw [Subgroup.top_lowerCentralSeries_one] at hf
  let _ := hf
  exact Set.toFinite _

end CriticalPercolation
end
end
end

end OAI
