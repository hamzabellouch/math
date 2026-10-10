import OAI.Analysis.KadisonKastler.ConjugatedWords
import OAI.Analysis.KadisonKastler.PublishedFock

namespace OAI

/-!
# Diagonal partitions conjugated by powers of a unitary

Conjugation preserves the projection partition and its tracial values.
Consequently the published faithful Fock representation applies to the
actual conjugated copies used in the phase coefficients, once scalar
freeness of those copies is supplied.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

universe u

section Ring

variable {α A : Type*} [Ring A] [StarRing A]

theorem conjugatedCopy_mul (e : α → A) (v : A) (hv : v ∈ unitary A)
    (n : ℕ) (a b : α) :
    conjugatedCopy e v n a * conjugatedCopy e v n b =
      star (v ^ n) * (e a * e b) * v ^ n := by
  have hp : v ^ n * star (v ^ n) = 1 :=
    Unitary.mul_star_self_of_mem ((unitary A).pow_mem hv n)
  unfold conjugatedCopy
  calc
    _ = star (v ^ n) * e a * (v ^ n * star (v ^ n)) * e b * v ^ n := by
      simp only [mul_assoc]
    _ = _ := by rw [hp, mul_one]; simp only [mul_assoc]

theorem conjugatedCopy_isStarProjection (e : α → A) (v : A) (hv : v ∈ unitary A)
    (n : ℕ) (a : α) (ha : IsStarProjection (e a)) :
    IsStarProjection (conjugatedCopy e v n a) where
  isIdempotentElem := by
    change conjugatedCopy e v n a * conjugatedCopy e v n a = _
    rw [conjugatedCopy_mul e v hv, ha.isIdempotentElem.eq]
    rfl
  isSelfAdjoint := by
    change star (conjugatedCopy e v n a) = conjugatedCopy e v n a
    simp only [conjugatedCopy, star_mul, star_star, ha.isSelfAdjoint.star_eq, mul_assoc]

theorem conjugatedCopy_orthogonal (e : α → A) (v : A) (hv : v ∈ unitary A)
    (n : ℕ) (a b : α) (hab : e a * e b = 0) :
    conjugatedCopy e v n a * conjugatedCopy e v n b = 0 := by
  rw [conjugatedCopy_mul e v hv, hab, mul_zero, zero_mul]

theorem sum_conjugatedCopy [Fintype α] (e : α → A) (v : A) (hv : v ∈ unitary A)
    (n : ℕ) (he : ∑ a, e a = 1) : ∑ a, conjugatedCopy e v n a = 1 := by
  calc
    _ = star (v ^ n) * (∑ a, e a) * v ^ n := by
      simp only [conjugatedCopy, sum_mul, mul_sum]
    _ = 1 := by
      rw [he, mul_one]
      exact Unitary.star_mul_self_of_mem ((unitary A).pow_mem hv n)

/-- The finite family appearing in a word of length `r`. -/
def conjugatedDiagonal (e : α → A) (v : A) (r : ℕ) (i : Fin r) (a : α) : A :=
  conjugatedCopy e v (r - 1 - i.val) a

theorem conjugatedProjectionWord_eq_diagonalWord (e : α → A) (v : A)
    {r : ℕ} (t : Fin r → α) :
    conjugatedProjectionWord e v t =
      (List.ofFn (fun i => conjugatedDiagonal e v r i (t i))).prod := rfl

end Ring

section Trace

variable {α : Type*} {B : Type u} [CStarAlgebra B]

/-- Traciality removes both factors of the conjugation. -/
theorem trace_conjugatedCopy (τ : FaithfulTracialState B) (e : α → B) (v : B)
    (hv : v ∈ unitary B) (n : ℕ) (a : α) :
    τ.toLinearMap (conjugatedCopy e v n a) = τ.toLinearMap (e a) := by
  unfold conjugatedCopy
  rw [τ.tracial (star (v ^ n) * e a) (v ^ n), ← mul_assoc,
    Unitary.mul_star_self_of_mem ((unitary B).pow_mem hv n), one_mul]

end Trace

section Coefficients

variable {B : Type u} [CStarAlgebra B] {r d : ℕ} [NeZero d]

/-- The positive phase coefficient satisfies the actual projection-word
bound, conditional only on the published Fock input and scalar freeness
of these specific conjugated diagonal copies. -/
theorem norm_positivePhaseCoefficient_le_of_published
    (hFock : PublishedDiagonalFockRepresentation.{u})
    (τ : FaithfulTracialState B) (e : Fin d → B) (v : B) (hv : v ∈ unitary B)
    (hprojection : ∀ a, IsStarProjection (e a))
    (horthogonal : ∀ a b, a ≠ b → e a * e b = 0)
    (hsum : ∑ a, e a = 1)
    (htrace : ∀ a, τ.toLinearMap (e a) = (d : ℂ)⁻¹)
    (hfree : ScalarFreeDiagonal τ (conjugatedDiagonal e v r))
    (hr : 1 ≤ r) (hd : freeWordThreshold r ≤ d) (s : Sym (Fin d) r) :
    ‖positivePhaseCoefficient e v r s‖ ≤ projectionWordWeight (freeWordC r) s := by
  rw [norm_positivePhaseCoefficient_eq_sum_conjugated e v hv]
  have h := norm_freeProjectionWords_le_of_published hFock τ (conjugatedDiagonal e v r)
    (fun i a => conjugatedCopy_isStarProjection e v hv (r - 1 - i.val) a (hprojection a))
    (fun i a b hab => conjugatedCopy_orthogonal e v hv (r - 1 - i.val) a b
      (horthogonal a b hab))
    (fun i => sum_conjugatedCopy e v hv (r - 1 - i.val) hsum)
    (fun i a => (trace_conjugatedCopy τ e v hv (r - 1 - i.val) a).trans (htrace a))
    hfree hr hd s
  simpa only [conjugatedProjectionWord_eq_diagonalWord] using h

/-- The adjoint formula gives the identical bound for negative powers. -/
theorem norm_negativePhaseCoefficient_le_of_published
    (hFock : PublishedDiagonalFockRepresentation.{u})
    (τ : FaithfulTracialState B) (e : Fin d → B) (v : B) (hv : v ∈ unitary B)
    (hprojection : ∀ a, IsStarProjection (e a))
    (horthogonal : ∀ a b, a ≠ b → e a * e b = 0)
    (hsum : ∑ a, e a = 1)
    (htrace : ∀ a, τ.toLinearMap (e a) = (d : ℂ)⁻¹)
    (hfree : ScalarFreeDiagonal τ (conjugatedDiagonal e v r))
    (hr : 1 ≤ r) (hd : freeWordThreshold r ≤ d) (s : Sym (Fin d) r) :
    ‖negativePhaseCoefficient e v r s‖ ≤ projectionWordWeight (freeWordC r) s := by
  rw [norm_negativePhaseCoefficient_eq_positive e v hv]
  exact norm_positivePhaseCoefficient_le_of_published hFock τ e v hv
    hprojection horthogonal hsum htrace hfree hr hd s

end Coefficients

end

end KadisonKastler

end OAI
