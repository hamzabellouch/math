import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneCharacter

namespace OAI

/-! # Gluing compatible integral characters over an exhaustive subgroup chain -/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance] Classical.propDecidable

variable {G : Type} [Group G] (S : ℕ → Subgroup G)
  (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (χ : ∀ n, S n →* ℤ)
  (hχ : ∀ i j (hij : i ≤ j) (g : S i), χ j (Subgroup.inclusion (hS hij) g) = χ i g)

def exhaustiveCharacterValue (g : G) : ℤ :=
  χ (Nat.find (hcover g)) ⟨g, Nat.find_spec (hcover g)⟩

include hS hχ in
theorem exhaustiveCharacterValue_eq (g : G) (n : ℕ) (hg : g ∈ S n) :
    exhaustiveCharacterValue S hcover χ g = χ n ⟨g, hg⟩ := by
  let i := Nat.find (hcover g)
  have hi : g ∈ S i := Nat.find_spec (hcover g)
  have h₁ := hχ i (max i n) (le_max_left _ _) ⟨g, hi⟩
  have h₂ := hχ n (max i n) (le_max_right _ _) ⟨g, hg⟩
  exact h₁.symm.trans h₂

def exhaustiveCharacter : G →* ℤ where
  toFun := exhaustiveCharacterValue S hcover χ
  map_one' := by
    rw [exhaustiveCharacterValue_eq S hS hcover χ hχ 1 0 (S 0).one_mem]
    exact (χ 0).map_one
  map_mul' g h := by
    let i := Nat.find (hcover g)
    let j := Nat.find (hcover h)
    let n := max i j
    have hg : g ∈ S n := hS (le_max_left i j) (Nat.find_spec (hcover g))
    have hh : h ∈ S n := hS (le_max_right i j) (Nat.find_spec (hcover h))
    rw [exhaustiveCharacterValue_eq S hS hcover χ hχ (g * h) n ((S n).mul_mem hg hh),
      exhaustiveCharacterValue_eq S hS hcover χ hχ g n hg,
      exhaustiveCharacterValue_eq S hS hcover χ hχ h n hh]
    exact (χ n).map_mul ⟨g, hg⟩ ⟨h, hh⟩

theorem exhaustiveCharacter_restrict (n : ℕ) :
    (exhaustiveCharacter S hS hcover χ hχ).comp (S n).subtype = χ n := by
  ext g
  exact exhaustiveCharacterValue_eq S hS hcover χ hχ g n g.property

end PolycyclicRecognition

end

end OAI
