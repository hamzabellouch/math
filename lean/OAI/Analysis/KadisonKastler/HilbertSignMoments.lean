import OAI.Analysis.KadisonKastler.FiniteSignFourthMoment

namespace OAI

/-! # Hilbert-space second and fourth moments of independent signs

The fourth-moment constant is three. Real Hilbert spaces suffice for the
proof and complex Hilbert spaces are covered by restriction of scalars.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Hilbert-space sum of independent signs. -/
def hilbertSignSum (a : ι → V) (ε : ι → Bool) : V :=
  ∑ i, finiteSign ε i • a i

/-- The variance-one normalized Hilbert-space sign sum. -/
def normalizedHilbertSignSum (a : ι → V) (ε : ι → Bool) : V :=
  (Real.sqrt (Fintype.card ι : ℝ))⁻¹ • hilbertSignSum a ε

omit [DecidableEq ι] in
private theorem sign_norm_sq (a : ι → V) (ε : ι → Bool) :
    ‖hilbertSignSum a ε‖ ^ 2 =
      ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) * inner ℝ (a i) (a j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [hilbertSignSum, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [real_inner_comm (a j) (a i)]
    ring

/-- Sign orthogonality gives the exact second moment. -/
theorem expect_hilbertSignSum_sq (a : ι → V) :
    (𝔼 ε : ι → Bool, ‖hilbertSignSum a ε‖ ^ 2) = ∑ i, ‖a i‖ ^ 2 := by
  simp_rw [sign_norm_sq]
  simp only [Finset.expect_sum_comm, ← Finset.expect_mul, finiteSign_pair]
  simp

omit [DecidableEq ι] in
private theorem sign_norm_fourth (a : ι → V) (ε : ι → Bool) :
    ‖hilbertSignSum a ε‖ ^ 4 =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l) *
          (inner ℝ (a i) (a j) * inner ℝ (a k) (a l)) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sign_norm_sq, pow_two, Finset.sum_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Hilbert-space fourth moments require no operator trace. -/
theorem expect_hilbertSignSum_fourth_le (a : ι → V) :
    (𝔼 ε : ι → Bool, ‖hilbertSignSum a ε‖ ^ 4) ≤
      3 * (∑ i, ‖a i‖ ^ 2) ^ 2 := by
  simp_rw [sign_norm_fourth]
  rw [expect_finiteSign_four_sum]
  have hmain : (∑ i, ∑ j, inner ℝ (a i) (a i) * inner ℝ (a j) (a j)) =
      (∑ i, ‖a i‖ ^ 2) ^ 2 := by
    simp only [real_inner_self_eq_norm_sq]
    rw [pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hpair : (∑ i, ∑ j, inner ℝ (a i) (a j) * inner ℝ (a i) (a j)) ≤
      (∑ i, ‖a i‖ ^ 2) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (norm_nonneg (inner ℝ (a i) (a j)))
      (norm_inner_le_norm (𝕜 := ℝ) (a i) (a j)) 2
    rw [Real.norm_eq_abs, sq_abs, mul_pow] at h
    simpa only [pow_two] using h
  have hother : (∑ i, ∑ j, inner ℝ (a i) (a j) * inner ℝ (a j) (a i)) =
      ∑ i, ∑ j, inner ℝ (a i) (a j) * inner ℝ (a i) (a j) := by
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [real_inner_comm (a j) (a i)]
  have hdiag : 0 ≤ ∑ i, inner ℝ (a i) (a i) * inner ℝ (a i) (a i) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [hmain, hother]
  linarith

/-- Exact normalized second moment. -/
theorem expect_normalizedHilbertSignSum_sq (a : ι → V) :
    (𝔼 ε : ι → Bool, ‖normalizedHilbertSignSum a ε‖ ^ 2) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖a i‖ ^ 2 := by
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [normalizedHilbertSignSum, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_expect, hs, expect_hilbertSignSum_sq]

/-- Normalized fourth moment is at most three times the second moment
squared, for every finite family of Hilbert vectors. -/
theorem expect_normalizedHilbertSignSum_fourth_le (a : ι → V) :
    (𝔼 ε : ι → Bool, ‖normalizedHilbertSignSum a ε‖ ^ 4) ≤
      3 * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖a i‖ ^ 2) ^ 2 := by
  have hs : |(Real.sqrt (Fintype.card ι : ℝ))⁻¹| ^ 4 =
      (Fintype.card ι : ℝ)⁻¹ ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), inv_pow]
  simp only [normalizedHilbertSignSum, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [← Finset.mul_expect, hs]
  have h := mul_le_mul_of_nonneg_left (expect_hilbertSignSum_fourth_le a)
    (sq_nonneg ((Fintype.card ι : ℝ)⁻¹))
  convert h using 1
  ring

end

end KadisonKastler

end OAI
