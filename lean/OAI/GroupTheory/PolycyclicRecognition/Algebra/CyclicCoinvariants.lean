import Mathlib.RepresentationTheory.Coinvariants

namespace OAI

/-! # Coinvariants of an infinite or finite cyclic group -/

noncomputable section
namespace PolycyclicRecognition

open Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

theorem cyclic_coinvariantsKer_eq_range (ρ : Representation k G V) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Coinvariants.ker ρ = LinearMap.range (ρ g - LinearMap.id) := by
  have hnat (n : ℕ) (v : V) :
      ρ (g ^ n) v - v ∈ LinearMap.range (ρ g - LinearMap.id) := by
    cases n with
    | zero => simp
    | succ n =>
        exact ⟨_, ρ.apply_sub_id_partialSum_eq n g v⟩
  have hint (n : ℤ) (v : V) :
      ρ (g ^ n) v - v ∈ LinearMap.range (ρ g - LinearMap.id) := by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa only [zpow_natCast] using hnat m v
    · have hc : ρ (g ^ m) (ρ ((g ^ m)⁻¹) v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      have hp := hnat m (ρ ((g ^ m)⁻¹) v)
      rw [hc] at hp
      simpa only [zpow_neg, zpow_natCast, neg_sub] using
        (LinearMap.range (ρ g - LinearMap.id)).neg_mem hp
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    obtain ⟨n, rfl⟩ := hg a
    exact hint n v
  · rintro _ ⟨v, rfl⟩
    exact Coinvariants.sub_mem_ker g v

end PolycyclicRecognition

end

end OAI
