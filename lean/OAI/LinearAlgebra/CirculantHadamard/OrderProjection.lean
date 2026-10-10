import OAI.LinearAlgebra.CirculantHadamard.CyclicNorm
import OAI.LinearAlgebra.CirculantHadamard.ProjectionCoefficients
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.NormNum

namespace OAI

universe uα

/-!
# The first order projection

The quotient sends the original cyclic generator to the cyclic generator of
the smaller order. Its coefficients are the sums over the actual reduction
fibers. When `n = m * d`, every fiber contains exactly `d` original indices;
an odd number of signs therefore produces an odd integer coefficient.

The norm scalar is preserved by the quotient map. In particular, projecting
from `2^(2*s) * u^2` to `2^(2*s)` does not divide the original norm scalar.
-/

noncomputable section

namespace CirculantHadamard

open scoped BigOperators

/-- Every fiber of reduction modulo a divisor has the exact quotient size. -/
theorem cyclic_reduction_fiber_card {n m d : ℕ} [NeZero n] [NeZero m]
    (hdiv : m ∣ n) (hn : n = m * d) (a : ZMod m) :
    Fintype.card {x : ZMod n // ZMod.castHom hdiv (ZMod m) x = a} = d := by
  classical
  let q : ZMod n →+ ZMod m := (ZMod.castHom hdiv (ZMod m)).toAddMonoidHom
  have hsurj : Function.Surjective q := by
    intro b
    refine ⟨(b.val : ZMod n), ?_⟩
    change ZMod.castHom hdiv (ZMod m) (b.val : ZMod n) = b
    simp only [map_natCast, ZMod.natCast_zmod_val]
  have hcards (b : ZMod m) :
      (Finset.univ.filter (fun x : ZMod n => q x = b)).card =
        (Finset.univ.filter (fun x : ZMod n => q x = a)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range q (hsurj b) (hsurj a)
  have htotal : n = m * (Finset.univ.filter (fun x : ZMod n => q x = a)).card := by
    calc
      n = (Finset.univ : Finset (ZMod n)).card := by simp
      _ = ∑ b : ZMod m, (Finset.univ.filter (fun x : ZMod n => q x = b)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = m * (Finset.univ.filter (fun x : ZMod n => q x = a)).card := by
        simp only [hcards, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  rw [Fintype.card_subtype]
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos m) (htotal.symm.trans hn)

/-- An odd finite family of actual integer signs has odd sum. -/
theorem odd_sum_of_signs {α : Type uα} [Fintype α] (f : α → ℤ)
    (hf : ∀ x, IsSign (f x)) (hcard : Odd (Fintype.card α)) :
    Odd (∑ x, f x) := by
  classical
  apply Int.odd_iff.mpr
  have hmod (x : α) : f x % 2 = 1 := by
    rcases hf x with hx | hx <;> norm_num [hx]
  calc
    (∑ x, f x) % 2 = (∑ _x : α, (1 : ℤ)) % 2 := by
      rw [Finset.sum_int_mod]
      simp only [hmod]
    _ = (Fintype.card α : ℤ) % 2 := by simp
    _ = 1 := Int.odd_iff.mp ((Int.odd_coe_nat _).mpr hcard)

/-- The actual quotient coefficient is odd because its fiber consists of
exactly the specified odd number of original signs. -/
theorem cyclicProjection_odd_coefficients {n m d : ℕ} [NeZero n] [NeZero m]
    (hdiv : m ∣ n) (hn : n = m * d) (hd : Odd d)
    (f : CyclicRing.Elem ℤ n) (hf : CyclicSignRow f) (a : ZMod m) :
    Odd ((cyclicProjection ℤ hdiv f).coeff a) := by
  classical
  rw [cyclicProjection_apply_fiber]
  apply odd_sum_of_signs
    (α := {x : ZMod n // ZMod.castHom hdiv (ZMod m) x = a})
    (fun x => f.coeff x.val) (fun x => hf x.val)
  rw [cyclic_reduction_fiber_card hdiv hn a]
  exact hd

/-- First projection in the order reduction: every coefficient is odd and
the scalar on the right of the norm equation remains the original order. -/
theorem exists_odd_cyclic_projection {n s u : ℕ} [NeZero n]
    (hu : Odd u) (heq : n = 2 ^ (2 * s) * u ^ 2)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    ∃ T : CyclicRing.Elem ℤ (2 ^ (2 * s)),
      (∀ a, Odd (T.coeff a)) ∧
        T * CyclicRing.ringStar T =
          CyclicRing.scalar _ ((2 ^ (2 * s) * u ^ 2 : ℕ) : ℤ) := by
  let : NeZero (2 ^ (2 * s)) := ⟨pow_ne_zero _ (by decide)⟩
  have hdiv : 2 ^ (2 * s) ∣ n := ⟨u ^ 2, heq⟩
  refine ⟨cyclicProjection ℤ hdiv f, ?_, ?_⟩
  · exact cyclicProjection_odd_coefficients hdiv heq hu.pow f hsign
  · calc
      _ = CyclicRing.scalar _ (n : ℤ) := cyclicProjection_norm hdiv hnorm
      _ = CyclicRing.scalar _ ((2 ^ (2 * s) * u ^ 2 : ℕ) : ℤ) := by rw [heq]

end CirculantHadamard

end

end OAI
