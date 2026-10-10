import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeExpectation

namespace OAI

/-! Inner-product recursion for reduced words. Freeness alone supplies
orthogonality at different first factors and contraction of matching first
letters. These are the algebraic identities needed for the tensor model. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τ : R →ₗ[ℂ] ℂ} {A D : StarSubalgebra ℂ R}

omit [Algebra ℂ R] [StarModule ℂ R] in
theorem star_list_prod (xs : List R) :
    star xs.prod = (xs.reverse.map star).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.reverse_cons, ih]

theorem AlternatingCenteredWord.star_reverse_append
    (hstar : ∀ x, τ (star x) = star (τ x))
    {side : Bool} {xs ys : List R}
    (hxs : AlternatingCenteredWord τ A D side xs)
    (hys : AlternatingCenteredWord τ A D (!side) ys) :
    ∃ s, AlternatingCenteredWord τ A D s (xs.reverse.map star ++ ys) := by
  induction hxs generalizing ys with
  | nil side => exact ⟨!side, by simpa using hys⟩
  | @cons side x xs hx hx0 hxs ih =>
    have hxstar : AlternatingCenteredWord τ A D side (star x :: ys) :=
      .cons (star_mem hx) (by rw [hstar, hx0, star_zero]) hys
    obtain ⟨s, hs⟩ := ih (ys := star x :: ys) (by simpa using hxstar)
    refine ⟨s, ?_⟩
    simpa only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append] using hs

theorem ScalarFree.trace_of_nonempty (hf : ScalarFree τ A D)
    {side : Bool} {xs : List R} (hx : AlternatingCenteredWord τ A D side xs)
    (hne : xs ≠ []) : τ xs.prod = 0 := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs => exact hf side x xs hx

theorem ScalarFree.trace_opposite_words (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x))
    {side : Bool} {xs ys : List R}
    (hxs : AlternatingCenteredWord τ A D side xs)
    (hys : AlternatingCenteredWord τ A D (!side) ys)
    (hne : xs ≠ [] ∨ ys ≠ []) : τ (star xs.prod * ys.prod) = 0 := by
  obtain ⟨s, hs⟩ := hxs.star_reverse_append hstar hys
  have hn : xs.reverse.map star ++ ys ≠ [] := by
    simp only [ne_eq, List.append_eq_nil_iff, List.map_eq_nil_iff,
      List.reverse_eq_nil_iff]
    tauto
  have h := hf.trace_of_nonempty hs hn
  simpa only [List.prod_append, ← star_list_prod] using h

theorem ScalarFree.trace_centered_sandwich (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x))
    {side : Bool} {xs ys : List R} {b : R}
    (hxs : AlternatingCenteredWord τ A D (!side) xs)
    (hys : AlternatingCenteredWord τ A D (!side) ys)
    (hb : b ∈ if side then A else D) (hb0 : τ b = 0) :
    τ (star xs.prod * b * ys.prod) = 0 := by
  have hy : AlternatingCenteredWord τ A D side (b :: ys) := .cons hb hb0 hys
  have h := hf.trace_opposite_words hstar hxs (by simpa using hy)
    (Or.inr (List.cons_ne_nil b ys))
  simpa only [List.prod_cons, mul_assoc] using h

theorem ScalarFree.trace_matching_heads (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {side : Bool} {xs ys : List R} {a b : R}
    (ha : a ∈ if side then A else D) (hb : b ∈ if side then A else D)
    (hxs : AlternatingCenteredWord τ A D (!side) xs)
    (hys : AlternatingCenteredWord τ A D (!side) ys) :
    τ (star (a :: xs).prod * (b :: ys).prod) =
      τ (star a * b) * τ (star xs.prod * ys.prod) := by
  have hsa : star a ∈ (if side then A else D : StarSubalgebra ℂ R) :=
    star_mem (s := (if side then A else D : StarSubalgebra ℂ R)) ha
  have hab : star a * b ∈ (if side then A else D : StarSubalgebra ℂ R) :=
    (if side then A else D : StarSubalgebra ℂ R).mul_mem hsa hb
  have hc := traceCentered_mem τ (if side then A else D) hab
  have hz := hf.trace_centered_sandwich hstar hxs hys hc
    (traceCentered_trace τ hτ (star a * b))
  have he : star (a :: xs).prod * (b :: ys).prod =
      star xs.prod * traceCentered τ (star a * b) * ys.prod +
        τ (star a * b) • (star xs.prod * ys.prod) := by
    calc
      _ = star xs.prod * (star a * b) * ys.prod := by
        simp only [List.prod_cons, star_mul]
        noncomm_ring
      _ = star xs.prod * (traceCentered τ (star a * b) +
          τ (star a * b) • 1) * ys.prod := by rw [traceCentered_add]
      _ = _ := by
        simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [he, map_add, hz, map_smul, zero_add, smul_eq_mul]

/-- The scalar product of two equally oriented centered words. Unequal
lengths give zero, including a nonempty word paired with the vacuum. -/
def centeredWordPairing (τ : R →ₗ[ℂ] ℂ) : List R → List R → ℂ
  | [], [] => 1
  | a :: xs, b :: ys => τ (star a * b) * centeredWordPairing τ xs ys
  | _, _ => 0

theorem ScalarFree.trace_same_words (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {side : Bool} {xs ys : List R}
    (hxs : AlternatingCenteredWord τ A D side xs)
    (hys : AlternatingCenteredWord τ A D side ys) :
    τ (star xs.prod * ys.prod) = centeredWordPairing τ xs ys := by
  induction hxs generalizing ys with
  | nil side =>
    cases hys with
    | nil => simpa [centeredWordPairing] using hτ
    | @cons _ y ys hy hy0 hys =>
      simpa only [centeredWordPairing] using
        hf.trace_opposite_words hstar (.nil (!side)) (by simpa using
          (AlternatingCenteredWord.cons hy hy0 hys)) (Or.inr (List.cons_ne_nil y ys))
  | @cons side x xs hx hx0 hxs ih =>
    cases hys with
    | nil =>
      simpa only [centeredWordPairing] using
        hf.trace_opposite_words hstar (.cons hx hx0 hxs) (.nil (!side))
          (Or.inl (List.cons_ne_nil x xs))
    | @cons _ y ys hy hy0 hys =>
      rw [hf.trace_matching_heads hstar hτ hx hy hxs hys, ih hys]
      rfl

omit [StarModule ℂ R] in
theorem centeredWordPairing_eq_zero_of_length_ne {xs ys : List R}
    (h : xs.length ≠ ys.length) : centeredWordPairing τ xs ys = 0 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact (h rfl).elim
    | cons => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hn : xs.length ≠ ys.length := by simpa using h
      simp only [centeredWordPairing, ih hn, mul_zero]

theorem ScalarFree.trace_words_of_length_ne (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {side : Bool} {xs ys : List R}
    (hxs : AlternatingCenteredWord τ A D side xs)
    (hys : AlternatingCenteredWord τ A D side ys) (h : xs.length ≠ ys.length) :
    τ (star xs.prod * ys.prod) = 0 := by
  rw [hf.trace_same_words hstar hτ hxs hys, centeredWordPairing_eq_zero_of_length_ne h]

omit [StarModule ℂ R] in
theorem centeredWordPairing_ofFn {n : ℕ} (a b : Fin n → R) :
    centeredWordPairing τ (List.ofFn a) (List.ofFn b) =
      ∏ i, τ (star (a i) * b i) := by
  induction n with
  | zero => simp [centeredWordPairing]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, centeredWordPairing, ih, Fin.prod_univ_succ]

theorem ScalarFree.trace_words_ofFn (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {side : Bool} {n : ℕ} (a b : Fin n → R)
    (ha : AlternatingCenteredWord τ A D side (List.ofFn a))
    (hb : AlternatingCenteredWord τ A D side (List.ofFn b)) :
    τ (star (List.ofFn a).prod * (List.ofFn b).prod) =
      ∏ i, τ (star (a i) * b i) := by
  rw [hf.trace_same_words hstar hτ ha hb, centeredWordPairing_ofFn]

end KadisonSimilarity

end

end OAI
