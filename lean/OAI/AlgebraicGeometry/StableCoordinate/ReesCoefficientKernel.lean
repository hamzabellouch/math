import OAI.AlgebraicGeometry.StableCoordinate.FilteredRees
import Mathlib.Tactic

namespace OAI

/-!
# Coefficientwise kernel and homogeneous independence for the Rees model

The kernel of the Rees specialization is detected one coefficient at a time.
This supplies the directness of homogeneous components without assuming an
associated-graded decomposition as an extra interface.
-/

namespace StableCoordinate.FilteredRees

open AddMonoidAlgebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (F : ℤ → Submodule k A) [SetLike.GradedMonoid F]

/-- An arbitrary Rees element vanishes after specialization by `T` exactly when
each coefficient belongs to the previous filtration step. -/
theorem mk_eq_zero_iff_coeff (hmono : Monotone F) (p : rees F) :
    Ideal.Quotient.mk (parameterIdeal F hmono) p = 0 ↔
      ∀ d : ℤ, (p : LaurentPolynomial A).coeff d ∈ F (d - 1) := by
  rw [Ideal.Quotient.eq_zero_iff_mem, parameterIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩ d
    have he := congrArg (fun r : rees F => (r : LaurentPolynomial A).coeff d) hq
    change (p : LaurentPolynomial A).coeff d =
      (AddMonoidAlgebra.single 1 1 * (q : LaurentPolynomial A)).coeff d at he
    rw [AddMonoidAlgebra.coeff_single_mul_apply] at he
    have he' : (p : LaurentPolynomial A).coeff d =
        (q : LaurentPolynomial A).coeff (d - 1) := by
      simpa only [one_mul, sub_eq_add_neg, add_comm] using he
    rw [he']
    exact q.property (d - 1)
  · intro hp
    let q : rees F := ⟨AddMonoidAlgebra.single (-1) 1 * (p : LaurentPolynomial A), by
      intro d
      rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
      have hd := hp (1 + d)
      simpa using hd⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change (p : LaurentPolynomial A) = AddMonoidAlgebra.single 1 1 *
      (AddMonoidAlgebra.single (-1) 1 * (p : LaurentPolynomial A))
    rw [← mul_assoc, AddMonoidAlgebra.single_mul_single]
    simp

/-- A finite sum of distinct homogeneous initial forms vanishes if and only if
all of those initial forms vanish, expressed by lower-filtration membership. -/
theorem sum_initial_eq_zero_iff (hmono : Monotone F) (s : Finset ℤ)
    (a : (d : ℤ) → F d) :
    (∑ d ∈ s, initial F hmono d (a d)) = 0 ↔
      ∀ d ∈ s, (a d : A) ∈ F (d - 1) := by
  classical
  have hcoeff (d : ℤ) :
      ((∑ i ∈ s, homogeneous F i (a i) : rees F) : LaurentPolynomial A).coeff d =
        if d ∈ s then (a d : A) else 0 := by
    change ((rees F).val (∑ i ∈ s, homogeneous F i (a i))).coeff d = _
    rw [map_sum]
    change (∑ i ∈ s, AddMonoidAlgebra.single i (a i : A) : LaurentPolynomial A).coeff d = _
    simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
    exact Finset.sum_ite_eq' s d (fun i => (a i : A))
  have hmk : (∑ d ∈ s, initial F hmono d (a d)) =
      Ideal.Quotient.mk (parameterIdeal F hmono) (∑ d ∈ s, homogeneous F d (a d)) := by
    simp only [map_sum, initial]
  rw [hmk, mk_eq_zero_iff_coeff]
  constructor
  · intro h d hd
    have h' := h d
    simpa only [hcoeff, ite_eq_left hd] using h'
  · intro h d
    rw [hcoeff]
    split_ifs with hd
    · exact h d hd
    · exact (F (d - 1)).zero_mem

/-- The homogeneous pieces are linearly independent in the actual Rees quotient. -/
theorem sum_initial_eq_zero_iff_individual (hmono : Monotone F) (s : Finset ℤ)
    (a : (d : ℤ) → F d) :
    (∑ d ∈ s, initial F hmono d (a d)) = 0 ↔
      ∀ d ∈ s, initial F hmono d (a d) = 0 := by
  simp only [sum_initial_eq_zero_iff, initial_eq_zero_iff]

end StableCoordinate.FilteredRees

end OAI
