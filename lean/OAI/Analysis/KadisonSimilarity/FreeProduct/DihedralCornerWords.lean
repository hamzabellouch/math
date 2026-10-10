import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeExpectation

namespace OAI

/-! The algebraic even-word step in the dihedral corner argument.
Corner letters absorb the reflection on the right, leaving an explicitly
alternating centered word in the original free factors. -/

noncomputable section
namespace KadisonSimilarity
namespace DihedralCornerWords

variable {R : Type*}

/-- The alternating word containing `n` copies of the pair `d,s`. -/
def pairLetters (d s : R) : ℕ → List R
  | 0 => []
  | n + 1 => d :: s :: pairLetters d s n

/-- A positive-power corner block, after absorbing its first reflection. -/
def blockLetters (d s a : R) (l : ℕ) : List R :=
  a :: s :: pairLetters d s (l - 1)

/-- Concatenate the explicitly alternating expansions of all corner blocks. -/
def productLetters (d s : R) (blocks : List (R × ℕ)) : List R :=
  blocks.flatMap fun b => blockLetters d s b.1 b.2

section Products
variable [Monoid R]

@[simp] theorem pairLetters_prod (d s : R) (n : ℕ) :
    (pairLetters d s n).prod = (d * s) ^ n := by
  induction n with
  | zero => simp [pairLetters]
  | succ n ih =>
    simp only [pairLetters, List.prod_cons, ih, pow_succ', mul_assoc]

/-- The corner relation `a*d=a` is exactly what removes the first `d`. -/
theorem blockLetters_prod (d s a : R) {l : ℕ} (hl : 0 < l) (had : a * d = a) :
    (blockLetters d s a l).prod = a * (d * s) ^ l := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  simp only [blockLetters, Nat.succ_sub_one, List.prod_cons, pairLetters_prod,
    pow_succ', ← mul_assoc, had]

/-- The concatenated centered word has precisely the original ordered
product of corner letters and positive rotation powers. -/
theorem productLetters_prod (d s : R) (blocks : List (R × ℕ))
    (hpositive : ∀ b ∈ blocks, 0 < b.2) (habsorb : ∀ b ∈ blocks, b.1 * d = b.1) :
    (productLetters d s blocks).prod = (blocks.map fun b => b.1 * (d * s) ^ b.2).prod := by
  induction blocks with
  | nil => simp [productLetters]
  | cons b bs ih =>
    simp only [productLetters, List.flatMap_cons, List.prod_append,
      List.map_cons, List.prod_cons]
    rw [blockLetters_prod d s b.1 (hpositive b List.mem_cons_self)
      (habsorb b List.mem_cons_self)]
    congr 1
    exact ih (fun b hb => hpositive b (List.mem_cons_of_mem _ hb))
      (fun b hb => habsorb b (List.mem_cons_of_mem _ hb))

/-- Intermediate right support factors disappear because each subsequent
letter is left supported on the same idempotent. No idempotence is needed
for this purely multiplicative identity. -/
theorem product_insert_right_support (p : R) (xs : List R) (hne : xs ≠ [])
    (hleft : ∀ x ∈ xs, p * x = x) :
    (xs.map fun x => x * p).prod = xs.prod * p := by
  induction xs with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [List.map_cons, List.prod_cons,
        ih (List.cons_ne_nil _ _) (fun z hz => hleft z (List.mem_cons_of_mem _ hz))]
      simp only [List.prod_cons]
      calc
        (x * p) * ((y * ys.prod) * p) = (x * (p * y)) * ys.prod * p := by
          simp only [mul_assoc]
        _ = (x * (y * ys.prod)) * p := by
          rw [hleft y (by simp)]
          simp only [mul_assoc]

end Products

section Freeness
variable [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  (τ : R →ₗ[ℂ] ℂ) (D A : StarSubalgebra ℂ R)
  {d s : R} (hd : d ∈ D) (hs : s ∈ A) (hd0 : τ d = 0) (hs0 : τ s = 0)

include hd hs hd0 hs0 in
/-- Prepending any number of `d,s` pairs preserves the alternating starting
side because each such pair has even length. -/
theorem pairLetters_prepend (n : ℕ) (tail : List R)
    (htail : AlternatingCenteredWord τ D A true tail) :
    AlternatingCenteredWord τ D A true (pairLetters d s n ++ tail) := by
  induction n with
  | zero => simpa only [pairLetters, List.nil_append] using htail
  | succ n ih =>
    change AlternatingCenteredWord τ D A true (d :: s :: (pairLetters d s n ++ tail))
    exact .cons (by simpa using hd) hd0 (.cons (by simpa using hs) hs0 ih)

include hd hs hd0 hs0 in
/-- A centered corner letter followed by `s` and rotation pairs is an
alternating centered word, ready to concatenate with another block. -/
theorem blockLetters_prepend (a : R) (ha : a ∈ D) (ha0 : τ a = 0)
    (l : ℕ) (tail : List R) (htail : AlternatingCenteredWord τ D A true tail) :
    AlternatingCenteredWord τ D A true (blockLetters d s a l ++ tail) := by
  change AlternatingCenteredWord τ D A true (a :: s :: (pairLetters d s (l - 1) ++ tail))
  exact .cons (by simpa using ha) ha0 (.cons (by simpa using hs) hs0
    (pairLetters_prepend τ D A hd hs hd0 hs0 (l - 1) tail htail))

include hd hs hd0 hs0 in
/-- The entire expanded corner product is alternating and centered in the
original two free algebras. -/
theorem productLetters_alternating (blocks : List (R × ℕ))
    (hmem : ∀ b ∈ blocks, b.1 ∈ D) (hzero : ∀ b ∈ blocks, τ b.1 = 0) :
    AlternatingCenteredWord τ D A true (productLetters d s blocks) := by
  induction blocks with
  | nil => exact .nil true
  | cons b bs ih =>
    change AlternatingCenteredWord τ D A true
      (blockLetters d s b.1 b.2 ++ productLetters d s bs)
    exact blockLetters_prepend τ D A hd hs hd0 hs0 b.1 (hmem b List.mem_cons_self)
      (hzero b List.mem_cons_self) b.2 _
      (ih (fun b hb => hmem b (List.mem_cons_of_mem _ hb))
        (fun b hb => hzero b (List.mem_cons_of_mem _ hb)))

omit [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
/-- A nonempty list of corner blocks produces a nonempty centered word. -/
theorem productLetters_ne_nil {blocks : List (R × ℕ)} (hblocks : blocks ≠ []) :
    productLetters d s blocks ≠ [] := by
  cases blocks with
  | nil => exact (hblocks rfl).elim
  | cons b bs => simp [productLetters, blockLetters]

include hd hs hd0 hs0 in
/-- The original algebraic corner-freeness step: every cyclic product of
centered corner letters and positive rotation powers has trace zero. -/
theorem trace_product_eq_zero (hf : ScalarFree τ D A)
    (blocks : List (R × ℕ)) (hblocks : blocks ≠ [])
    (hmem : ∀ b ∈ blocks, b.1 ∈ D) (hzero : ∀ b ∈ blocks, τ b.1 = 0)
    (hpositive : ∀ b ∈ blocks, 0 < b.2) (habsorb : ∀ b ∈ blocks, b.1 * d = b.1) :
    τ ((blocks.map fun b => b.1 * (d * s) ^ b.2).prod) = 0 := by
  have hw := productLetters_alternating τ D A hd hs hd0 hs0 blocks hmem hzero
  have hne := productLetters_ne_nil (d := d) (s := s) hblocks
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  rw [hx] at hw
  rw [← productLetters_prod d s blocks hpositive habsorb, hx]
  exact hf true x xs hw

omit [StarRing R] [StarModule ℂ R] in
/-- For a tracial functional, inserting the common corner support after
each letter does not change the trace of a nonempty product. -/
theorem trace_product_insert_right_support
    (htr : ∀ x y, τ (x * y) = τ (y * x)) (p : R)
    (xs : List R) (hne : xs ≠ []) (hleft : ∀ x ∈ xs, p * x = x) :
    τ ((xs.map fun x => x * p).prod) = τ xs.prod := by
  rw [product_insert_right_support p xs hne hleft, htr]
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs =>
    simp only [List.prod_cons, ← mul_assoc, hleft x List.mem_cons_self]

include hd hs hd0 hs0 in
/-- The even cyclic trace vanishing remains true with all the actual corner
supports inserted. -/
theorem trace_corner_product_eq_zero (hf : ScalarFree τ D A)
    (htr : ∀ x y, τ (x * y) = τ (y * x)) (p : R)
    (blocks : List (R × ℕ)) (hblocks : blocks ≠ [])
    (hmem : ∀ b ∈ blocks, b.1 ∈ D) (hzero : ∀ b ∈ blocks, τ b.1 = 0)
    (hpositive : ∀ b ∈ blocks, 0 < b.2) (habsorb : ∀ b ∈ blocks, b.1 * d = b.1)
    (hleft : ∀ b ∈ blocks, p * b.1 = b.1) :
    τ ((blocks.map fun b => b.1 * (d * s) ^ b.2 * p).prod) = 0 := by
  let xs := blocks.map fun b => b.1 * (d * s) ^ b.2
  have hne : xs ≠ [] := by simpa only [xs, ne_eq, List.map_eq_nil_iff] using hblocks
  have hsupp : ∀ x ∈ xs, p * x = x := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    rw [← mul_assoc, hleft b hb]
  have h := trace_product_insert_right_support τ htr p xs hne hsupp
  simp only [xs, List.map_map, Function.comp_def] at h
  rw [h]
  exact trace_product_eq_zero τ D A hd hs hd0 hs0 hf blocks hblocks hmem hzero
    hpositive habsorb

end Freeness
end DihedralCornerWords
end KadisonSimilarity

end

end OAI
