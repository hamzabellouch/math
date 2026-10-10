import OAI.Analysis.KadisonSimilarity.FreeProduct.FreePairWords
import Mathlib.Algebra.Star.Unitary

namespace OAI

/-! Orthogonal conjugates of reduced words. These are the finite-word
calculations used to identify the center of the generated free algebra. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τ : R →ₗ[ℂ] ℂ} {A D : StarSubalgebra ℂ R}

theorem CenteredPairWord.append_pair {xs : List R}
    (hxs : CenteredPairWord τ A D xs) {a d : R}
    (ha : a ∈ A) (hd : d ∈ D) (ha0 : τ a = 0) (hd0 : τ d = 0) :
    CenteredPairWord τ A D (xs ++ [a, d]) := by
  induction hxs with
  | nil => exact .cons ha hd ha0 hd0 .nil
  | cons ha' hd' ha0' hd0' _ ih => exact .cons ha' hd' ha0' hd0' ih

/-- A nonempty pair word has a last centered pair. -/
theorem CenteredPairWord.nil_or_snoc {xs : List R}
    (hxs : CenteredPairWord τ A D xs) :
    xs = [] ∨ ∃ ys a d, CenteredPairWord τ A D ys ∧ a ∈ A ∧ d ∈ D ∧
      τ a = 0 ∧ τ d = 0 ∧ xs = ys ++ [a, d] := by
  induction hxs with
  | nil => exact Or.inl rfl
  | @cons a d xs ha hd ha0 hd0 hxs ih =>
    right
    rcases ih with hnil | ⟨ys, b, e, hys, hb, he, hb0, he0, hsnoc⟩
    · subst xs
      exact ⟨[], a, d, .nil, ha, hd, ha0, hd0, rfl⟩
    · exact ⟨a :: d :: ys, b, e, .cons ha hd ha0 hd0 hys,
        hb, he, hb0, he0, by simp only [hsnoc, List.cons_append]⟩

omit [StarModule ℂ R] in
theorem centeredWordPairing_append_pair (xs : List R) (a b c d : R) :
    centeredWordPairing τ (xs ++ [a, b]) (xs ++ [c, d]) =
      centeredWordPairing τ xs xs * τ (star a * c) * τ (star b * d) := by
  induction xs with
  | nil => simp [centeredWordPairing]
  | cons x xs ih =>
    simp only [List.cons_append, centeredWordPairing, ih]
    ring

/-- Conjugating a reduced word by orthogonal centered unitaries gives
orthogonal words, even when its first other-factor endpoint is unrestricted. -/
theorem ScalarFree.trace_conjugate_words_zero (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (h1 : τ 1 = 1)
    {xs : List R} (hxs : CenteredPairWord τ A D xs)
    {b d u v : R} (hb : b ∈ A) (hb0 : τ b = 0) (hd : d ∈ D)
    (hu : u ∈ D) (hv : v ∈ D) (hu0 : τ u = 0) (hv0 : τ v = 0)
    (huv : τ (u * star v) = 0) :
    τ (star (u * d * xs.prod * b * star u) *
      (v * d * xs.prod * b * star v)) = 0 := by
  have hx := hxs.append_pair hb (star_mem (s := D) hu) hb0 (by rw [hstar, hu0, star_zero])
  have hy := hxs.append_pair hb (star_mem (s := D) hv) hb0 (by rw [hstar, hv0, star_zero])
  have h := hf.trace_matching_heads hstar h1
    (side := false) (by exact D.mul_mem hu hd) (by exact D.mul_mem hv hd)
    hx.alternating hy.alternating
  rw [hf.trace_same_words hstar h1 hx.alternating hy.alternating,
    centeredWordPairing_append_pair, star_star, huv, mul_zero, mul_zero] at h
  simpa only [List.prod_cons, List.prod_append, List.prod_nil, mul_one, mul_assoc] using h

omit [StarModule ℂ R] in
/-- A central trace pairing is unchanged by unitary conjugation. -/
theorem trace_central_conjugate
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (c w : R) (u : unitary R) (hc : star c * (u : R) = (u : R) * star c) :
    τ (star c * ((u : R) * w * star (u : R))) = τ (star c * w) := by
  calc
    _ = τ ((star c * (u : R)) * w * star (u : R)) := by
      simp only [mul_assoc]
    _ = τ ((u : R) * (star c * w * star (u : R))) := by rw [hc]; simp only [mul_assoc]
    _ = τ ((star c * w * star (u : R)) * (u : R)) := htr _ _
    _ = τ (star c * w) := by rw [mul_assoc, u.property.1, mul_one]

omit [StarModule ℂ R] in
/-- Cyclicity alone makes a trace invariant under unitary conjugation. -/
theorem trace_unitary_conjugate
    (htr : ∀ a b, τ (a * b) = τ (b * a)) (w : R) (u : unitary R) :
    τ ((u : R) * w * star (u : R)) = τ w := by
  rw [htr, ← mul_assoc, u.property.1, one_mul]

end KadisonSimilarity

end

end OAI
