import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.EncodingDegree

variable {R : Type*} [CommSemiring R]
variable {S K B : Type*} [Fintype S] [DecidableEq S] [Fintype K]

/-- A coefficient expansion has weighted degree given by the sum of the weights
of its assigned vector blocks. The coefficients can be arbitrary. -/
theorem weightedHomogeneous_expansion (c : (S → K) → R) (blocks : S → B)
    (w : B → ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun x : B × K => w x.1)
      (∑ k : S → K, MvPolynomial.C (c k) *
        ∏ i : S, MvPolynomial.X (blocks i, k i))
      (∑ i : S, w (blocks i)) := by
  classical
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro k _
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro i _
  exact MvPolynomial.isWeightedHomogeneous_X _ _ _

/-- The degree in one block is exactly the number of occurrences of that block. -/
theorem blockHomogeneous_expansion [DecidableEq B]
    (c : (S → K) → R) (blocks : S → B) (b : B) :
    MvPolynomial.IsWeightedHomogeneous
      (fun x : B × K => if x.1 = b then 1 else 0)
      (∑ k : S → K, MvPolynomial.C (c k) *
        ∏ i : S, MvPolynomial.X (blocks i, k i))
      (Finset.univ.filter (fun i => blocks i = b)).card := by
  simpa only [Finset.sum_boole, Nat.cast_id] using
    (weightedHomogeneous_expansion c blocks (fun x => if x = b then 1 else 0))

/-- Changing a single assigned block changes the weight by exactly the
corresponding source/destination contribution. This form avoids truncated subtraction. -/
theorem sum_weight_update (blocks : S → B) (w : B → ℕ)
    (i : S) (b : B) :
    (∑ j : S, w ((Function.update blocks i b) j)) + w (blocks i) =
      (∑ j : S, w (blocks j)) + w b := by
  classical
  have h1 := Finset.sum_erase_add (s := Finset.univ) (f := fun j => w ((Function.update blocks i b) j)) (Finset.mem_univ i)
  have h2 := Finset.sum_erase_add (s := Finset.univ) (f := fun j => w (blocks j)) (Finset.mem_univ i)
  have h : (∑ j ∈ Finset.univ.erase i, w ((Function.update blocks i b) j)) =
      ∑ j ∈ Finset.univ.erase i, w (blocks j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  simp only [Function.update_self] at h1
  omega

end Problem346.EncodingDegree

end

end OAI
