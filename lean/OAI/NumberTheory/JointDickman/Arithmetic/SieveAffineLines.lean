import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace OAI

/-! # Cardinality of a proper affine line over a prime residue field -/

namespace JointDickman

open Finset

noncomputable def affineResidueLine {p : ℕ} [NeZero p] (a b c : ZMod p) :
    Finset (ZMod p × ZMod p) := univ.filter (fun x => a * x.1 + b * x.2 = c)

/-- A proper affine line has at most `p` residue pairs. -/
theorem affineResidueLine_card_le {p : ℕ} (hp : p.Prime)
    (a b c : ZMod p) (hproper : a ≠ 0 ∨ b ≠ 0) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (affineResidueLine a b c).card ≤ p := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  change (affineResidueLine a b c).card ≤ p
  rcases hproper with ha | hb
  · have hinj : Set.InjOn Prod.snd (↑(affineResidueLine a b c) : Set (ZMod p × ZMod p)) := by
      intro x hx y hy hxy
      apply Prod.ext _ hxy
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      rw [hxy] at hx'
      have heq : a * x.1 = a * y.1 := by linear_combination hx' - hy'
      exact mul_left_cancel₀ ha heq
    calc
      _ = ((affineResidueLine a b c).image Prod.snd).card := (card_image_iff.mpr hinj).symm
      _ ≤ (univ : Finset (ZMod p)).card := card_le_card (subset_univ _)
      _ = p := by simp
  · have hinj : Set.InjOn Prod.fst (↑(affineResidueLine a b c) : Set (ZMod p × ZMod p)) := by
      intro x hx y hy hxy
      apply Prod.ext hxy
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      rw [hxy] at hx'
      have heq : b * x.2 = b * y.2 := by linear_combination hx' - hy'
      exact mul_left_cancel₀ hb heq
    calc
      _ = ((affineResidueLine a b c).image Prod.fst).card := (card_image_iff.mpr hinj).symm
      _ ≤ (univ : Finset (ZMod p)).card := card_le_card (subset_univ _)
      _ = p := by simp

end JointDickman

end OAI
