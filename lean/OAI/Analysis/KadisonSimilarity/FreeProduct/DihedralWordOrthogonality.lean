import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeDihedral

namespace OAI

/-!
# Orthogonality of the actual dihedral word inclusions

Alternating-centered-word freeness computes the tracial pairing of the words
`e (s d)^k a`. The algebraic calculation only needs `e` in the first free
algebra; its projection and support properties enter when these pairings are
used to construct the normalized Hilbert-space inclusions.
-/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

private def dihedralPairs (x y : R) : ℕ → List R
  | 0 => []
  | n + 1 => x :: y :: dihedralPairs x y n

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
private theorem dihedralPairs_prod (x y : R) (n : ℕ) :
    (dihedralPairs x y n).prod = (x * y) ^ n := by
  induction n with
  | zero => simp [dihedralPairs]
  | succ n ih => simp only [dihedralPairs, List.prod_cons, ih, pow_succ']; simp [mul_assoc]

private def dihedralSandwich (d s e : R) : ℕ → ℕ → List R
  | 0, j => e :: dihedralPairs s d j
  | k + 1, j => d :: s :: dihedralSandwich d s e k j

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
private theorem dihedralSandwich_prod (d s e : R) (k j : ℕ) :
    (dihedralSandwich d s e k j).prod = (d * s) ^ k * e * (s * d) ^ j := by
  induction k with
  | zero => simp [dihedralSandwich, dihedralPairs_prod]
  | succ k ih =>
    simp only [dihedralSandwich, List.prod_cons, ih, pow_succ']
    simp only [mul_assoc]

variable (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
  {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
  {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0)

include hd hs hd0 hs0 in
private theorem dihedralPairs_left_alternating (n : ℕ) :
    AlternatingCenteredWord τ P Q true (dihedralPairs d s n) := by
  induction n with
  | zero => exact .nil true
  | succ n ih => exact .cons (by simpa) hd0 (.cons (by simpa) hs0 ih)

include hd hs hd0 hs0 in
private theorem dihedralPairs_right_alternating (n : ℕ) :
    AlternatingCenteredWord τ P Q false (dihedralPairs s d n) := by
  induction n with
  | zero => exact .nil false
  | succ n ih => exact .cons (by simpa) hs0 (.cons (by simpa) hd0 ih)

include hd hs hd0 hs0 in
private theorem dihedralSandwich_alternating {e : R} (he : e ∈ P) (he0 : τ e = 0)
    (k j : ℕ) : AlternatingCenteredWord τ P Q true (dihedralSandwich d s e k j) := by
  induction k with
  | zero => exact .cons (by simpa) he0 (dihedralPairs_right_alternating τ hd hs hd0 hs0 j)
  | succ k ih => exact .cons (by simpa) hd0 (.cons (by simpa) hs0 ih)

include hf in
private theorem trace_nonempty_alternating (side : Bool) (xs : List R)
    (hxs : xs ≠ []) (halt : AlternatingCenteredWord τ P Q side xs) : τ xs.prod = 0 := by
  obtain ⟨x, tail, rfl⟩ := List.exists_cons_of_ne_nil hxs
  exact hf side x tail halt

include hd hs hd0 hs0 in
private theorem dihedralPairs_append_alternating {a : R} (ha : a ∈ Q) (ha0 : τ a = 0)
    (n : ℕ) : AlternatingCenteredWord τ P Q false (dihedralPairs s d n ++ [a]) := by
  induction n with
  | zero => exact .cons (by simpa) ha0 (.nil true)
  | succ n ih => exact .cons (by simpa) hs0 (.cons (by simpa) hd0 ih)

include hτ hf hd hs hd0 hs0 in
/-- Every positive residual dihedral power pairs trivially with the entire
second algebra, from either orientation. -/
theorem trace_test_dihedral_power (htr : ∀ a b, τ (a * b) = τ (b * a))
    {a : R} (ha : a ∈ Q) {n : ℕ} (hn : 0 < n) :
    τ (a * (d * s) ^ n) = 0 ∧ τ (a * (s * d) ^ n) = 0 := by
  have ha0 := traceCentered_trace τ hτ a
  have ham := traceCentered_mem τ Q ha
  have hp : τ (traceCentered τ a * (d * s) ^ n) = 0 := by
    have hw := hf false (traceCentered τ a) (dihedralPairs d s n)
      (.cons (by simpa using ham) ha0 (dihedralPairs_left_alternating τ hd hs hd0 hs0 n))
    simpa only [List.prod_cons, dihedralPairs_prod] using hw
  have hm : τ ((s * d) ^ n * traceCentered τ a) = 0 := by
    have hw := trace_nonempty_alternating τ hf false
      (dihedralPairs s d n ++ [traceCentered τ a]) (by simp)
      (dihedralPairs_append_alternating τ hd hs hd0 hs0 ham ha0 n)
    simpa only [List.prod_append, List.prod_singleton, dihedralPairs_prod] using hw
  have hpp := hf.trace_pair_power hd hs hd0 hs0 hn
  have hmp := hf.symm.trace_pair_power hs hd hs0 hd0 hn
  constructor
  · rw [← traceCentered_add τ a, add_mul, smul_mul_assoc, one_mul, map_add, map_smul,
      hp, hpp, smul_zero, add_zero]
  · rw [htr a ((s * d) ^ n), ← traceCentered_add τ a, mul_add, mul_smul_comm,
      mul_one, map_add, map_smul, hm, hmp, smul_zero, add_zero]

include hτ hf hd hs hd0 hs0 in
/-- A centered first-algebra letter between the two dihedral halves has zero
trace against every second-algebra coefficient. -/
theorem trace_centered_dihedral_sandwich {e a : R} (he : e ∈ P) (he0 : τ e = 0)
    (ha : a ∈ Q) (k j : ℕ) : τ (a * ((d * s) ^ k * e * (s * d) ^ j)) = 0 := by
  have halt := dihedralSandwich_alternating τ hd hs hd0 hs0 he he0 k j
  have hnonempty : dihedralSandwich d s e k j ≠ [] := by
    cases k <;> simp [dihedralSandwich]
  have heword : τ ((d * s) ^ k * e * (s * d) ^ j) = 0 := by
    simpa only [dihedralSandwich_prod] using trace_nonempty_alternating τ hf true _ hnonempty halt
  have haword : τ (traceCentered τ a * ((d * s) ^ k * e * (s * d) ^ j)) = 0 := by
    have h := hf false (traceCentered τ a) (dihedralSandwich d s e k j)
      (.cons (by simpa using traceCentered_mem τ Q ha) (traceCentered_trace τ hτ a) halt)
    simpa only [List.prod_cons, dihedralSandwich_prod] using h
  rw [← traceCentered_add τ a, add_mul, smul_mul_assoc, one_mul, map_add, map_smul,
    haword, heword, smul_zero, add_zero]

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
private theorem dihedral_cancel_successors (hdd : d * d = 1) (hss : s * s = 1)
    (k j : ℕ) : (d * s) ^ (k + 1) * (s * d) ^ (j + 1) = (d * s) ^ k * (s * d) ^ j := by
  have hxy : (d * s) * (s * d) = 1 := by
    rw [mul_assoc d s (s * d), ← mul_assoc s s d, hss, one_mul, hdd]
  rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc (d * s) (s * d), hxy, one_mul]

include hτ hf hd hs hd0 hs0 in
theorem trace_test_dihedral_product (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hdd : d * d = 1) (hss : s * s = 1) {a : R} (ha : a ∈ Q) (k j : ℕ) :
    τ (a * ((d * s) ^ k * (s * d) ^ j)) = if k = j then τ a else 0 := by
  induction k generalizing j with
  | zero =>
    cases j with
    | zero => simp
    | succ j =>
      simpa using (trace_test_dihedral_power τ hτ hf hd hs hd0 hs0 htr ha (Nat.succ_pos j)).2
  | succ k ih =>
    cases j with
    | zero =>
      simpa using (trace_test_dihedral_power τ hτ hf hd hs hd0 hs0 htr ha (Nat.succ_pos k)).1
    | succ j =>
      rw [dihedral_cancel_successors hdd hss]
      simpa only [Nat.succ.injEq] using ih j

include hτ hf hd hs hd0 hs0 in
/-- The scalar trace of the middle letter is the only surviving contribution
to the diagonal word pairing. -/
theorem trace_dihedral_sandwich (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hdd : d * d = 1) (hss : s * s = 1) {e a : R} (he : e ∈ P) (ha : a ∈ Q)
    (k j : ℕ) :
    τ (a * ((d * s) ^ k * e * (s * d) ^ j)) = if k = j then τ e * τ a else 0 := by
  have hexpand : a * ((d * s) ^ k * e * (s * d) ^ j) =
      a * ((d * s) ^ k * traceCentered τ e * (s * d) ^ j) +
      τ e • (a * ((d * s) ^ k * (s * d) ^ j)) := by
    conv_lhs => rw [← traceCentered_add τ e]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [hexpand, map_add, map_smul,
    trace_centered_dihedral_sandwich τ hτ hf hd hs hd0 hs0
      (traceCentered_mem τ P he) (traceCentered_trace τ hτ e) ha,
    trace_test_dihedral_product τ hτ hf hd hs hd0 hs0 htr hdd hss ha, zero_add]
  split_ifs <;> simp_all only [smul_eq_mul, mul_zero]

include hτ hf hd hs hd0 hs0 in
/-- The exact inner-product identity for the unnormalized word maps
`v ↦ e (s d)^k v`. No projection or support hypothesis on `e` is needed for
this tracial sandwich identity. -/
theorem dihedral_word_pairing (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hdd : d * d = 1) (hss : s * s = 1) {e v w : R}
    (he : e ∈ P) (hv : v ∈ Q) (hw : w ∈ Q) (k j : ℕ) :
    τ (star v * (d * s) ^ k * e * (s * d) ^ j * w) =
      if k = j then τ e * τ (star v * w) else 0 := by
  calc
    _ = τ (w * (star v * (d * s) ^ k * e * (s * d) ^ j)) := htr _ w
    _ = τ ((w * star v) * ((d * s) ^ k * e * (s * d) ^ j)) := by
      congr 1
      simp only [mul_assoc]
    _ = if k = j then τ e * τ (w * star v) else 0 :=
      trace_dihedral_sandwich τ hτ hf hd hs hd0 hs0 htr hdd hss he
        (Q.mul_mem hw (show star v ∈ Q from star_mem hv)) k j
    _ = _ := by rw [htr w (star v)]

end KadisonSimilarity

end

end OAI
