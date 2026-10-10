import Mathlib

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

lemma cyclic_mod_torsion_of_finite_kernel {G A : Type*} [Group G] [Group A]
    (ρ : G →* A) (hρ : Surjective ρ) (φ : A →* Multiplicative ℤ)
    (hφ : Surjective φ) (hk : (φ.ker : Set A).Finite) :
    ∃ g : G, ∀ a : G, ∃ k : ℤ, IsOfFinOrder (ρ (a*g^(-k))) := by
  obtain ⟨g,hg⟩ := hφ.comp hρ (Multiplicative.ofAdd (1 : ℤ))
  change φ (ρ g)=Multiplicative.ofAdd (1 : ℤ) at hg
  let _ := hk.to_subtype
  refine ⟨g,fun a => ?_⟩
  let k := (φ (ρ a)).toAdd
  refine ⟨k,?_⟩
  have he : ρ (a*g^(-k))∈φ.ker := by
    change φ (ρ (a*g^(-k)))=1
    rw [map_mul,map_zpow,map_mul,map_zpow,hg]
    change (φ (ρ a)).toAdd+(-k) • (1 : ℤ)=0
    simp [k]
  obtain ⟨m,hm,heq⟩ :=
    (isOfFinOrder_of_finite (⟨ρ (a*g^(-k)),he⟩ : φ.ker)).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,congrArg Subtype.val heq⟩

end CriticalPercolation
end
end
end

end OAI
