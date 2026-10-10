import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

namespace OAI

/-! # Coordinate independence in finite product samples

Uniformly sampling a finite function is the concrete probability space
used for the independent left and right matrix unitaries. One- and
two-coordinate expectations reduce to their actual finite averages.
-/

namespace KadisonKastler

open scoped BigOperators

section

variable {I G X : Type*} [Fintype I] [DecidableEq I]
  [Fintype G] [Nonempty G] [AddCommMonoid X] [Module ℚ≥0 X]

/-- One coordinate of a uniformly sampled function has the uniform law. -/
theorem expect_sample_coordinate (i : I) (f : G → X) :
    (𝔼 ω : I → G, f (ω i)) = 𝔼 g : G, f g := by
  have he := Fintype.expect_equiv (Equiv.funSplitAt i G)
    (fun ω : I → G => f (ω i))
    (fun p : G × ({j : I // j ≠ i} → G) => f p.1) (fun _ => rfl)
  rw [he]
  have hp := Finset.expect_product (Finset.univ : Finset G)
    (Finset.univ : Finset ({j : I // j ≠ i} → G))
    (fun p : G × ({j : I // j ≠ i} → G) => f p.1)
  simpa only [Finset.univ_product_univ, Fintype.expect_const] using hp

/-- Distinct coordinates in the finite product are independent. -/
theorem expect_sample_two_coordinates {i j : I} (hij : i ≠ j) (f : G → G → X) :
    (𝔼 ω : I → G, f (ω i) (ω j)) = 𝔼 g : G, 𝔼 h : G, f g h := by
  have he := Fintype.expect_equiv (Equiv.funSplitAt i G)
    (fun ω : I → G => f (ω i) (ω j))
    (fun p : G × ({k : I // k ≠ i} → G) => f p.1 (p.2 ⟨j, Ne.symm hij⟩))
    (fun _ => rfl)
  rw [he]
  have hp := Finset.expect_product (Finset.univ : Finset G)
    (Finset.univ : Finset ({k : I // k ≠ i} → G))
    (fun p : G × ({k : I // k ≠ i} → G) => f p.1 (p.2 ⟨j, Ne.symm hij⟩))
  rw [show (𝔼 p : G × ({k : I // k ≠ i} → G), f p.1 (p.2 ⟨j, Ne.symm hij⟩)) =
      𝔼 g : G, 𝔼 ω : ({k : I // k ≠ i} → G), f g (ω ⟨j, Ne.symm hij⟩) from
    by simpa only [Finset.univ_product_univ] using hp]
  simp_rw [expect_sample_coordinate]

end

section

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [Nonempty G]

/-- Summing the two-coordinate law separates the diagonal samples from
the independent off-diagonal samples, with their exact multiplicities. -/
theorem expect_sample_pair_sum (f : G → G → ℝ) :
    (𝔼 ω : I → G, ∑ i, ∑ j, f (ω i) (ω j)) =
      (Fintype.card I : ℝ) * (𝔼 g : G, f g g) +
        (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) *
          (𝔼 g : G, 𝔼 h : G, f g h) := by
  simp only [Finset.expect_sum_comm]
  let d : ℝ := 𝔼 g : G, f g g
  let c : ℝ := 𝔼 g : G, 𝔼 h : G, f g h
  have hp (i j : I) : (𝔼 ω : I → G, f (ω i) (ω j)) =
      if i = j then d else c := by
    by_cases h : i = j
    · subst j
      simpa only [ite_true, d] using expect_sample_coordinate (G := G) i (fun g => f g g)
    · simpa only [h, ite_false, c] using expect_sample_two_coordinates h f
  simp_rw [hp]
  have hi (i j : I) : (if i = j then d else c) = c + (if i = j then d - c else 0) := by
    split_ifs <;> ring
  simp_rw [hi, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) * c) +
    (Fintype.card I : ℝ) * (d - c) = _
  dsimp only [d, c]
  ring

end

end KadisonKastler

end OAI
