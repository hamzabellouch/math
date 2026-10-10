import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExhaustionOrientation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyClassExhaustion

namespace OAI

/-! # Detecting the orientation by nonzero top homology

A nonzero class survives in every sufficiently large stage of an exhaustion.
For rank-one integral coefficients, top duality at those stages identifies the
coefficient representation with the compatible orientation.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem exhaustion_orientation_of_nonzero_top
    (S : ℕ → Subgroup G) (hS : Monotone S) (hcover : ∀ g, ∃ i, g ∈ S i)
    (d : ℕ) (R : Rep ℤ G) (eR : R.V ≃ₗ[ℤ] ℤ)
    (hR : ∀ (i : ℕ) (A : Rep ℤ (S i)),
      Nonempty (groupHomology A d ≃ₗ[ℤ] (Rep.res (S i).subtype R ⟶ A)))
    (A : Rep ℤ G) (eA : A.V ≃ₗ[ℤ] ℤ)
    (x : groupHomology A d) (hx : x ≠ 0) : Nonempty (R ≅ A) := by
  obtain ⟨n, y, hy⟩ := exists_homologyClass_in_subgroup S hS hcover A d x
  have hk (k : ℕ) (hnk : n ≤ k) :
      Nonempty (Rep.res (S k).subtype R ≅ Rep.res (S k).subtype A) := by
    let z := groupHomology.map (Subgroup.inclusion (hS hnk))
      (subgroupRestrictionMap (hS hnk) A) d y
    have hz : z ≠ 0 := by
      intro hz
      apply hx
      have hf := congrArg (fun f => f y) (subgroupHomologyInclusion_factor (hS hnk) A d)
      change subgroupHomologyInclusion (S k) A d z =
        subgroupHomologyInclusion (S n) A d y at hf
      rw [hz, map_zero, hy] at hf
      exact hf.symm
    obtain ⟨e⟩ := hR k (Rep.res (S k).subtype A)
    have hf : e z ≠ 0 := by
      intro hf
      exact hz (e.injective (hf.trans (map_zero e).symm))
    exact rankOne_rep_iso_of_nonzero _ _ eR eA (e z) hf
  have hχ : rankOneCharacter R eR = rankOneCharacter A eA := by
    ext g
    obtain ⟨m, hm⟩ := hcover g
    let k := max n m
    obtain ⟨i⟩ := hk k (le_max_left _ _)
    have hkg : g ∈ S k := hS (le_max_right _ _) hm
    have hc := rankOneCharacter_eq_of_iso
      (Rep.res (S k).subtype R) (Rep.res (S k).subtype A) eR eA i
    exact congrArg (fun c : S k →* ℤ => c ⟨g, hkg⟩) hc
  exact ⟨rankOneCharacterIso R eR ≪≫
    eqToIso (congrArg scalarCharacterRep hχ) ≪≫ (rankOneCharacterIso A eA).symm⟩

end PolycyclicRecognition

end

end OAI
