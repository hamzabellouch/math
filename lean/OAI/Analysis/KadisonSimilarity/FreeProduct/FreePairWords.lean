import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeWordInnerProducts

namespace OAI

/-! The regrouped free-product words have centered pairs internally and
unrestricted endpoints. Their trace pairing is the tensor product pairing. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τ : R →ₗ[ℂ] ℂ} {A D : StarSubalgebra ℂ R}

/-- A sequence of centered `A,D` pairs, including the empty sequence. -/
inductive CenteredPairWord (τ : R →ₗ[ℂ] ℂ) (A D : StarSubalgebra ℂ R) : List R → Prop
  | nil : CenteredPairWord τ A D []
  | cons {a d : R} {xs : List R} (ha : a ∈ A) (hd : d ∈ D)
      (ha0 : τ a = 0) (hd0 : τ d = 0) (hxs : CenteredPairWord τ A D xs) :
      CenteredPairWord τ A D (a :: d :: xs)

namespace CenteredPairWord

theorem alternating {xs : List R} (h : CenteredPairWord τ A D xs) :
    AlternatingCenteredWord τ A D true xs := by
  induction h with
  | nil => exact .nil true
  | cons ha hd ha0 hd0 _ ih =>
    exact .cons ha ha0 (.cons hd hd0 ih)

theorem alternating_append {xs : List R} (h : CenteredPairWord τ A D xs)
    {r : R} (hr : r ∈ A) (hr0 : τ r = 0) :
    AlternatingCenteredWord τ A D true (xs ++ [r]) := by
  induction h with
  | nil => exact .cons hr hr0 (.nil false)
  | cons ha hd ha0 hd0 _ ih =>
    exact .cons ha ha0 (.cons hd hd0 ih)

theorem even_length {xs : List R} (h : CenteredPairWord τ A D xs) :
    ∃ n : ℕ, xs.length = 2 * n := by
  induction h with
  | nil => exact ⟨0, rfl⟩
  | cons _ _ _ _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp only [List.length_cons]; omega⟩

end CenteredPairWord

theorem ScalarFree.trace_pairWords_right_centered (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {xs ys : List R} (hxs : CenteredPairWord τ A D xs)
    (hys : CenteredPairWord τ A D ys) {r : R} (hr : r ∈ A) (hr0 : τ r = 0) :
    τ (star xs.prod * ys.prod * r) = 0 := by
  have hlen : xs.length ≠ (ys ++ [r]).length := by
    obtain ⟨n, hn⟩ := hxs.even_length
    obtain ⟨m, hm⟩ := hys.even_length
    simp only [List.length_append, List.length_singleton]
    omega
  have h := hf.trace_words_of_length_ne hstar hτ hxs.alternating
    (hys.alternating_append hr hr0) hlen
  simpa only [List.prod_append, List.prod_singleton, mul_assoc] using h

theorem ScalarFree.trace_pairWords_centered_middle (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x))
    {xs ys : List R} (hxs : CenteredPairWord τ A D xs)
    (hys : CenteredPairWord τ A D ys) {q r : R}
    (hq : q ∈ D) (hq0 : τ q = 0) (hr : r ∈ A) (hτ : τ 1 = 1) :
    τ (star xs.prod * q * ys.prod * r) = 0 := by
  have h0 := hf.trace_centered_sandwich hstar hxs.alternating hys.alternating
    (side := false) hq hq0
  have h1 := hf.trace_centered_sandwich hstar hxs.alternating
    (hys.alternating_append (traceCentered_mem τ A hr) (traceCentered_trace τ hτ r))
    (side := false) hq hq0
  have h1' : τ (star xs.prod * q * ys.prod * traceCentered τ r) = 0 := by
    simpa only [List.prod_append, List.prod_singleton, mul_assoc] using h1
  calc
    _ = τ (star xs.prod * q * ys.prod * traceCentered τ r) +
        τ r * τ (star xs.prod * q * ys.prod) := by
      conv_lhs => rw [← traceCentered_add τ r]
      rw [mul_add, mul_smul_comm, mul_one, map_add, map_smul, smul_eq_mul]
    _ = 0 := by rw [h1', h0, mul_zero, add_zero]

/-- Full endpoints factor off from the inner product of centered pair words. -/
theorem ScalarFree.trace_pairWords_endpoints (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {xs ys : List R} (hxs : CenteredPairWord τ A D xs)
    (hys : CenteredPairWord τ A D ys) {q r : R} (hq : q ∈ D) (hr : r ∈ A) :
    τ (star xs.prod * q * ys.prod * r) =
      τ q * τ r * centeredWordPairing τ xs ys := by
  have h0 := hf.trace_pairWords_centered_middle hstar hxs hys
    (traceCentered_mem τ D hq) (traceCentered_trace τ hτ q) hr hτ
  have h1 := hf.trace_pairWords_right_centered hstar hτ hxs hys
    (traceCentered_mem τ A hr) (traceCentered_trace τ hτ r)
  have he : τ (star xs.prod * ys.prod * r) =
      τ r * centeredWordPairing τ xs ys := by
    calc
      _ = τ (star xs.prod * ys.prod * traceCentered τ r) +
          τ r * τ (star xs.prod * ys.prod) := by
        conv_lhs => rw [← traceCentered_add τ r]
        rw [mul_add, mul_smul_comm, mul_one, map_add, map_smul, smul_eq_mul]
      _ = _ := by rw [h1, zero_add, hf.trace_same_words hstar hτ
        hxs.alternating hys.alternating]
  calc
    _ = τ (star xs.prod * traceCentered τ q * ys.prod * r) +
        τ q * τ (star xs.prod * ys.prod * r) := by
      conv_lhs => rw [← traceCentered_add τ q]
      rw [mul_add, add_mul, add_mul, mul_smul_comm, mul_one, smul_mul_assoc,
        smul_mul_assoc, map_add, map_smul, smul_eq_mul]
    _ = _ := by rw [h0, zero_add, he, mul_assoc]

/-- Interleave two equally long lists of letters in their original order. -/
def pairWord : {n : ℕ} → (Fin n → R) → (Fin n → R) → List R
  | 0, _, _ => []
  | _ + 1, a, d => a 0 :: d 0 :: pairWord (Fin.tail a) (Fin.tail d)

omit [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
@[simp] theorem length_pairWord {n : ℕ} (a d : Fin n → R) :
    (pairWord a d).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pairWord, List.length_cons, ih]; omega

theorem CenteredPairWord.of_pairWord {n : ℕ} (a d : Fin n → R)
    (ha : ∀ i, a i ∈ A) (hd : ∀ i, d i ∈ D)
    (ha0 : ∀ i, τ (a i) = 0) (hd0 : ∀ i, τ (d i) = 0) :
    CenteredPairWord τ A D (pairWord a d) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    exact .cons (ha 0) (hd 0) (ha0 0) (hd0 0)
      (ih _ _ (fun i => ha i.succ) (fun i => hd i.succ)
        (fun i => ha0 i.succ) (fun i => hd0 i.succ))

omit [StarModule ℂ R] in
theorem centeredWordPairing_pairWord {n : ℕ} (a d b e : Fin n → R) :
    centeredWordPairing τ (pairWord a d) (pairWord b e) =
      (∏ i, τ (star (a i) * b i)) * ∏ i, τ (star (d i) * e i) := by
  induction n with
  | zero => simp [pairWord, centeredWordPairing]
  | succ n ih =>
    simp only [pairWord, centeredWordPairing, ih, Fin.prod_univ_succ, Fin.tail]
    ring

/-- The actual trace inner product of words with unrestricted endpoints. -/
theorem ScalarFree.trace_full_pairWords (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    (htr : ∀ x y, τ (x * y) = τ (y * x))
    {xs ys : List R} (hxs : CenteredPairWord τ A D xs)
    (hys : CenteredPairWord τ A D ys) {d e b c : R}
    (hd : d ∈ D) (he : e ∈ D) (hb : b ∈ A) (hc : c ∈ A) :
    τ (star (d * xs.prod * b) * (e * ys.prod * c)) =
      τ (star d * e) * τ (star b * c) * centeredWordPairing τ xs ys := by
  calc
    _ = τ (star b * (star xs.prod * (star d * e) * ys.prod * c)) := by
      congr 1
      simp only [star_mul]
      noncomm_ring
    _ = τ (star xs.prod * (star d * e) * ys.prod * (c * star b)) := by
      rw [htr]
      congr 1
      noncomm_ring
    _ = τ (star d * e) * τ (c * star b) * centeredWordPairing τ xs ys :=
      hf.trace_pairWords_endpoints hstar hτ hxs hys
        (D.mul_mem (star_mem (s := D) hd) he)
        (A.mul_mem hc (star_mem (s := A) hb))
    _ = _ := by rw [htr c (star b)]

end KadisonSimilarity

end

end OAI
