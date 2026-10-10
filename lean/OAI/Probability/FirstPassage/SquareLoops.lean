import OAI.Probability.FirstPassage.BoundaryCycles
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace OAI

namespace PlanarFPP
open Finset

structure SquareLoop (m : ℕ) where
  side : Fin m → SquareSide
  follows : ∀ i, (side (finRotate m i)).tail = (side i).head

namespace SquareLoop
variable {m : ℕ}

def winding (c : SquareLoop m) : ℤ := ∑ i, (c.side i).rayCross

def NoRepeatedSides (c : SquareLoop m) : Prop := Function.Injective c.side

theorem sum_delta (c : SquareLoop m) : ∑ i, (c.side i).2.delta = 0 := by
  have h := congrArg (fun f : Fin m → Vertex => ∑ i, f i) (funext c.follows)
  simp only [SquareSide.head, sum_add_distrib] at h
  rw [Equiv.sum_comp (finRotate m) (fun i => (c.side i).tail)] at h
  exact add_left_cancel (show (∑ i, (c.side i).tail) + (∑ i, (c.side i).2.delta) =
      (∑ i, (c.side i).tail) + 0 by simpa using h.symm)

def upLeftIndices (c : SquareLoop m) : Finset (Fin m) :=
  univ.filter (fun i => (c.side i).2 = Step.north ∨ (c.side i).2 = Step.west)

theorem upLeft_count (c : SquareLoop m) : m = 2 * c.upLeftIndices.card := by
  have hx := congrArg Prod.fst c.sum_delta
  have hy := congrArg Prod.snd c.sum_delta
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero] at hx hy
  have hd (i : Fin m) : (1 : ℤ) =
      2 * (if (c.side i).2 = Step.north ∨ (c.side i).2 = Step.west then 1 else 0) -
        ((c.side i).2.delta.2 - (c.side i).2.delta.1) := by
    cases h : (c.side i).2 <;> simp [Step.delta]
  have hs := sum_congr (s₁ := (univ : Finset (Fin m))) rfl (fun i _ => hd i)
  simp only [sum_sub_distrib, hx, hy, sub_zero, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  have hc : (∑ i : Fin m,
      if (c.side i).2 = Step.north ∨ (c.side i).2 = Step.west then (1 : ℤ) else 0) =
      c.upLeftIndices.card := by
    simp [upLeftIndices, sum_boole]
  rw [← mul_sum, hc] at hs
  exact_mod_cast hs

def badSites (c : SquareLoop m) : Finset Vertex :=
  c.upLeftIndices.image (fun i => (c.side i).1)

theorem length_le_eight_badSites (c : SquareLoop m) (hc : c.NoRepeatedSides) :
    m ≤ 8*c.badSites.card := by
  have hs : c.upLeftIndices.image c.side ⊆ c.badSites ×ˢ (univ : Finset Step) := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    exact mem_product.mpr ⟨mem_image.mpr ⟨i,hi,rfl⟩, mem_univ _⟩
  have hn : (c.upLeftIndices.image c.side).card = c.upLeftIndices.card :=
    card_image_of_injective _ hc
  have hcard := card_le_card hs
  rw [hn, card_product] at hcard
  have hfour : (univ : Finset Step).card = 4 := by decide
  rw [hfour] at hcard
  have hh := c.upLeft_count
  omega

end SquareLoop

end PlanarFPP

end OAI
