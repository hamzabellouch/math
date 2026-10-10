import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthNoFreePair
import Mathlib.GroupTheory.CoprodI

namespace OAI

/-! # Polynomial growth excludes a pair of ping-pong transformations

This is the explicit bridge from contracting linear dynamics to the word-ball
counting obstruction. The free-group injection is the proved library
ping-pong lemma, and the exponential count is the actual positive-word count.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Pointwise Function

variable {G : Type} {X : Type*} [Group G] [DecidableEq G] [MulAction G X]

theorem polynomial_growth_excludes_ping_pong
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (a : Bool → G) (P N : Bool → Set X)
    (hP : ∀ i, (P i).Nonempty)
    (hPP : Pairwise (Disjoint on P)) (hNN : Pairwise (Disjoint on N))
    (hPN : ∀ i j, Disjoint (P i) (N j))
    (ha : ∀ i, a i • (N i)ᶜ ⊆ P i)
    (hai : ∀ i, a⁻¹ i • (P i)ᶜ ⊆ N i) : False := by
  exact polynomial_growth_no_free_pair S hS hgen hvol (FreeGroup.lift a)
    (FreeGroup.injective_lift_of_ping_pong a P N hP hPP hNN hPN ha hai)

end PolycyclicRecognition

end

end OAI
