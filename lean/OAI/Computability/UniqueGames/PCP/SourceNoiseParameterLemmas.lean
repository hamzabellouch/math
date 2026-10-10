import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

section

/-!
An executable finite-noise denominator for a positive rational target error.
Using the stored rational denominator avoids rounding, searches, and choice.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceNoiseParameter

/-- A positive rational has numerator at least one, so its reciprocal
denominator is no larger than the rational itself. Adding two also ensures
the noise parameter is at most one half for every input. -/
def noiseDenominator (ξ : ℚ) : ℕ := ξ.den + 2

theorem noiseDenominator_ge_two (ξ : ℚ) : 2 ≤ noiseDenominator ξ := by
  unfold noiseDenominator
  omega

theorem noiseDenominator_pos (ξ : ℚ) : 0 < noiseDenominator ξ :=
  lt_of_lt_of_le (by decide) (noiseDenominator_ge_two ξ)

theorem noiseDenominator_inv_pos (ξ : ℚ) :
    0 < (noiseDenominator ξ : ℚ)⁻¹ := by
  apply inv_pos.mpr
  exact_mod_cast noiseDenominator_pos ξ

theorem noiseDenominator_inv_le_half (ξ : ℚ) :
    (noiseDenominator ξ : ℚ)⁻¹ ≤ (1 / 2 : ℚ) := by
  rw [inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  exact_mod_cast noiseDenominator_ge_two ξ

/-- The actual computed reciprocal noise is below every positive target. -/
theorem noiseDenominator_inv_le {ξ : ℚ} (hξ : 0 < ξ) :
    (noiseDenominator ξ : ℚ)⁻¹ ≤ ξ := by
  have hn : (1 : ℤ) ≤ ξ.num := by
    have h := Rat.num_pos.mpr hξ
    omega
  have hnq : (1 : ℚ) ≤ (ξ.num : ℚ) := by exact_mod_cast hn
  have hd : (0 : ℚ) < (ξ.den : ℚ) := by exact_mod_cast ξ.den_pos
  calc
    (noiseDenominator ξ : ℚ)⁻¹ = 1 / (noiseDenominator ξ : ℚ) := inv_eq_one_div _
    _ ≤ 1 / (ξ.den : ℚ) := by
      apply one_div_le_one_div_of_le hd
      exact_mod_cast (show ξ.den ≤ noiseDenominator ξ by
        unfold noiseDenominator
        omega)
    _ ≤ (ξ.num : ℚ) / (ξ.den : ℚ) := div_le_div_of_nonneg_right hnq hd.le
    _ = ξ := ξ.num_div_den

end UniqueGamesTheorem.Foundations.Hastad.SourceNoiseParameter

end

section

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

theorem bitSign_xor (b c : Bool) :
    bitSign (b ^^ c) = bitSign b * bitSign c := by
  cases b <;> cases c <;> norm_num [bitSign]

def cubeXor {I : Type*} (x y : Cube I) : Cube I := fun i => x i ^^ y i

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

theorem walsh_symm {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x = walsh x s := by
  simp [walsh, Bool.and_comm]

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

theorem walsh_xor {I : Type*} [Fintype I] [DecidableEq I] (s x y : Cube I) :
    walsh s (cubeXor x y) = walsh s x * walsh s y := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [cubeXor]
  cases s i <;> cases x i <;> cases y i <;> norm_num [bitSign]

theorem coordinate_orthogonality (s t : Bool) :
    (∑ x : Bool, bitSign (s && x) * bitSign (t && x)) =
      if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [bitSign, Fintype.sum_bool]

theorem walsh_sum_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (∑ x, walsh s x * walsh t x) =
      if s = t then (Fintype.card (Cube I) : ℝ) else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    bitSign (s i && b) * bitSign (t i && b))]
  simp only [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

theorem walsh_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (𝔼 x, walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, walsh_sum_orthogonality]
  split_ifs <;> simp

def coefficient {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (s : Cube I) : ℝ :=
  𝔼 x, f x * walsh s x

theorem walsh_inversion {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (x : Cube I) :
    (∑ s, coefficient f s * walsh s x) = f x := by
  classical
  unfold coefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have h (y : Cube I) :
      (∑ s, (f y * walsh s y) * walsh s x) =
        f y * (if y = x then (Fintype.card (Cube I) : ℝ) else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [walsh_symm (x := y), walsh_symm (x := x)]
    exact walsh_sum_orthogonality y x
  simp_rw [h]
  rw [Fintype.expect_eq_sum_div_card]
  simp

theorem walsh_inner {I : Type*} [Fintype I] [DecidableEq I] (f g : Cube I → ℝ) :
    (∑ s, coefficient f s * coefficient g s) = 𝔼 x, f x * g x := by
  classical
  unfold coefficient
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  have h : (∑ s, (𝔼 y, f y * walsh s y) * (g x * walsh s x)) =
      g x * (∑ s, coefficient f s * walsh s x) := by
    simp only [Finset.mul_sum, coefficient]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h, walsh_inversion]
  ring

theorem walsh_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) :
    (∑ s, coefficient f s ^ 2) = 𝔼 x, f x ^ 2 := by
  simpa [pow_two] using walsh_inner f f

theorem sign_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → Bool) :
    (∑ s, coefficient (fun x => bitSign (f x)) s ^ 2) = 1 := by
  rw [walsh_parseval]
  simp

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def support (s : Cube I) : Finset I := Finset.univ.filter fun i => s i = true

def noiseWeight (ε : ℝ) (μ : Cube I) : ℝ :=
  ∏ i, if μ i then ε else 1 - ε

omit [DecidableEq I] in
theorem noiseWeight_nonneg {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) (μ : Cube I) :
    0 ≤ noiseWeight ε μ := by
  apply Finset.prod_nonneg
  intro i _
  split <;> linarith

theorem noiseWeight_sum (ε : ℝ) : (∑ μ : Cube I, noiseWeight ε μ) = 1 := by
  unfold noiseWeight
  rw [← Fintype.prod_sum (fun (_ : I) (b : Bool) => if b then ε else 1 - ε)]
  simp

theorem noise_walsh (ε : ℝ) (s : Cube I) :
    (∑ μ, noiseWeight ε μ * walsh s μ) = (1 - 2 * ε) ^ (support s).card := by
  unfold noiseWeight walsh
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b =>
    (if b then ε else 1 - ε) * bitSign (s i && b))]
  have hc (i : I) : (∑ b : Bool,
      (if b then ε else 1 - ε) * bitSign (s i && b)) =
        if s i then 1 - 2 * ε else 1 := by
    cases s i <;> simp [bitSign]
    ring
  simp_rw [hc]
  simp [support, Finset.prod_ite]

/-- The third queried Boolean table is `g * (f ∘ π) * μ` in sign notation. -/
def thirdQuery (π : J → I) (f : Cube I) (g μ : Cube J) : Cube J :=
  cubeXor g (cubeXor (fun y => f (π y)) μ)

/-- Walsh autocorrelation, proved by expanding the explicit basis. -/
theorem walsh_autocorrelation (B : Cube J → ℝ) (h : Cube J) :
    (𝔼 g, B g * B (cubeXor g h)) =
      ∑ s, coefficient B s ^ 2 * walsh s h := by
  conv_lhs =>
    enter [2, g, 2]
    rw [← walsh_inversion B (cubeXor g h)]
  simp_rw [Finset.mul_sum, walsh_xor]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm : (fun g => B g * (coefficient B s * (walsh s g * walsh s h))) =
      (fun g => (coefficient B s * walsh s h) * (B g * walsh s g)) := by
    funext g
    ring
  rw [hterm, ← Finset.mul_expect]
  change (coefficient B s * walsh s h) * coefficient B s = _
  ring

def projectedCoefficient (π : J → I) (A : Cube I → ℝ) (s : Cube J) : ℝ :=
  𝔼 f, A f * walsh s (fun y => f (π y))

def testBias (ε : ℝ) (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ * A f *
    (𝔼 g, B g * B (thirdQuery π f g μ))

theorem testBias_fourier (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → ℝ) :
    testBias ε π A B = ∑ s,
      projectedCoefficient π A s * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
  unfold testBias thirdQuery
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  conv_lhs =>
    enter [2, f]
    rw [Finset.sum_comm]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm (f : Cube I) :
      (∑ μ, noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * walsh s (cubeXor (fun y => f (π y)) μ))) =
      (A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
    simp_rw [walsh_xor]
    have heq (μ : Cube J) : noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * (walsh s (fun y => f (π y)) * walsh s μ)) =
      ((A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2) *
        (noiseWeight ε μ * walsh s μ) := by ring
    simp_rw [heq]
    rw [← Finset.mul_sum, noise_walsh]
  simp_rw [hterm, ← Finset.expect_mul]
  rfl

def testAcceptance (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ *
    (𝔼 g, if A f ^^ B g ^^ B (thirdQuery π f g μ) then 0 else 1)

theorem threeBit_indicator (a b c : Bool) :
    (if a ^^ b ^^ c then (0 : ℝ) else 1) =
      (1 + bitSign a * bitSign b * bitSign c) / 2 := by
  cases a <;> cases b <;> cases c <;> norm_num [bitSign]

/-- Actual acceptance is one half plus one half of the three-answer correlation. -/
theorem testAcceptance_eq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    testAcceptance ε π A B =
      (1 + testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g))) / 2 := by
  unfold testAcceptance testBias
  simp_rw [threeBit_indicator, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp only [Fintype.expect_const]
  have hterm (f : Cube I) (μ : Cube J) :
      noiseWeight ε μ * ((1 + 𝔼 g,
        bitSign (A f) * bitSign (B g) * bitSign (B (thirdQuery π f g μ))) * 2⁻¹) =
      (noiseWeight ε μ + noiseWeight ε μ * bitSign (A f) *
        (𝔼 g, bitSign (B g) * bitSign (B (thirdQuery π f g μ)))) * 2⁻¹ := by
    simp_rw [mul_assoc (bitSign (A f)), ← Finset.mul_expect]
    ring
  simp_rw [hterm, ← Finset.sum_mul, Finset.sum_add_distrib, noiseWeight_sum,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

/-! Explicit half-table storage, odd folding, and conditioning on the finite
set of satisfying local assignments for Håstad's test. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeFlip (f : Cube I) : Cube I := fun i => !(f i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeFlip_cubeFlip (f : Cube I) : cubeFlip (cubeFlip f) = f := by
  funext i
  simp [cubeFlip]

@[simp] theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

theorem sum_cubeFlip (F : Cube I → ℝ) : (∑ f, F (cubeFlip f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeFlip f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg cubeFlip h
    simpa only [cubeFlip_cubeFlip] using h'
  · intro g _
    exact ⟨cubeFlip g, Finset.mem_univ _, cubeFlip_cubeFlip g⟩
  · intro f _
    rfl

theorem coefficient_zero_of_odd (F : Cube I → ℝ)
    (hF : ∀ f, F (cubeFlip f) = -F f) :
    coefficient F (fun _ => false) = 0 := by
  have hs : (∑ f, F f) = 0 := by
    have h := sum_cubeFlip F
    simp_rw [hF, Finset.sum_neg_distrib] at h
    linarith
  simp [coefficient, walsh, bitSign, Fintype.expect_eq_sum_div_card, hs]

theorem coefficient_sign_zero_of_folded (A : Cube I → Bool)
    (hA : ∀ f, A (cubeFlip f) = !(A f)) :
    coefficient (fun f => bitSign (A f)) (fun _ => false) = 0 := by
  apply coefficient_zero_of_odd
  intro f
  rw [hA, bitSign_not]

def representative (i₀ : I) (f : Cube I) : Cube I :=
  if f i₀ then cubeFlip f else f

omit [Fintype I] [DecidableEq I] in
theorem representative_at (i₀ : I) (f : Cube I) :
    representative i₀ f i₀ = false := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

omit [Fintype I] [DecidableEq I] in
theorem representative_flip (i₀ : I) (f : Cube I) :
    representative i₀ (cubeFlip f) = representative i₀ f := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

abbrev HalfCube (i₀ : I) := {f : Cube I // f i₀ = false}

def canonicalInput (i₀ : I) (f : Cube I) : HalfCube i₀ :=
  ⟨representative i₀ f, representative_at i₀ f⟩

omit [Fintype I] [DecidableEq I] in
theorem canonicalInput_flip (i₀ : I) (f : Cube I) :
    canonicalInput i₀ (cubeFlip f) = canonicalInput i₀ f := by
  apply Subtype.ext
  exact representative_flip i₀ f

/-- One stored bit and one explicit sign correction for every queried table. -/
def foldedAnswer (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  table (canonicalInput i₀ f) ^^ f i₀

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_flip (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) :
    foldedAnswer i₀ table (cubeFlip f) = !(foldedAnswer i₀ table f) := by
  unfold foldedAnswer
  rw [canonicalInput_flip]
  change (table (canonicalInput i₀ f) ^^ !(f i₀)) =
    !(table (canonicalInput i₀ f) ^^ f i₀)
  cases table (canonicalInput i₀ f) <;> cases f i₀ <;> rfl

theorem foldedAnswer_zero_coefficient (i₀ : I) (table : HalfCube i₀ → Bool) :
    coefficient (fun f => bitSign (foldedAnswer i₀ table f)) (fun _ => false) = 0 :=
  coefficient_sign_zero_of_folded _ (foldedAnswer_flip i₀ table)

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_dictator (i₀ i : I) (f : Cube I) :
    foldedAnswer i₀ (fun h => h.val i) f = f i := by
  cases hf : f i₀ <;> cases hi : f i <;>
    simp [foldedAnswer, canonicalInput, representative, cubeFlip, hf, hi]

def coordinateMask (i : I) : Cube I := fun j => decide (j = i)

def cubeToggle (i : I) (f : Cube I) : Cube I :=
  cubeXor f (coordinateMask i)

omit [Fintype I] in
@[simp] theorem cubeToggle_twice (i : I) (f : Cube I) :
    cubeToggle i (cubeToggle i f) = f := by
  funext j
  change ((f j ^^ coordinateMask i j) ^^ coordinateMask i j) = f j
  cases f j <;> cases coordinateMask i j <;> rfl

theorem walsh_coordinateMask (s : Cube I) (i : I) :
    walsh s (coordinateMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [coordinateMask]
  · intro j _ hj
    simp [coordinateMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem walsh_cubeToggle (s : Cube I) (i : I) (f : Cube I) (hs : s i = true) :
    walsh s (cubeToggle i f) = -walsh s f := by
  rw [cubeToggle, walsh_xor, walsh_coordinateMask, hs]
  simp [bitSign]

theorem sum_cubeToggle (i : I) (F : Cube I → ℝ) :
    (∑ f, F (cubeToggle i f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeToggle i f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg (cubeToggle i) h
    simpa only [cubeToggle_twice] using h'
  · intro g _
    exact ⟨cubeToggle i g, Finset.mem_univ _, cubeToggle_twice i g⟩
  · intro f _
    rfl

def restrictQuery (valid : I → Bool) (f : Cube I) :
    Cube {i : I // valid i = true} := fun i => f i.val

omit [Fintype I] in
theorem restrictQuery_cubeToggle (valid : I → Bool) (i : I)
    (hi : valid i = false) (f : Cube I) :
    restrictQuery valid (cubeToggle i f) = restrictQuery valid f := by
  funext j
  have hj : j.val ≠ i := by
    intro heq
    have hp := j.property
    rw [heq, hi] at hp
    contradiction
  simp [restrictQuery, cubeToggle, cubeXor, coordinateMask, hj]

theorem conditioned_coefficient_zero_invalid (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I) (i : I)
    (hi : valid i = false) (hs : s i = true) :
    coefficient (fun f => B (restrictQuery valid f)) s = 0 := by
  have hsum := sum_cubeToggle i (fun f => B (restrictQuery valid f) * walsh s f)
  simp_rw [restrictQuery_cubeToggle valid i hi, walsh_cubeToggle s i _ hs,
    mul_neg, Finset.sum_neg_distrib] at hsum
  have hz : (∑ f, B (restrictQuery valid f) * walsh s f) = 0 := by linarith
  simp [coefficient, Fintype.expect_eq_sum_div_card, hz]

/-- Every coordinate returned from a nonzero conditioned Fourier mask is an
actual valid local assignment, proved from the concrete restriction map. -/
theorem conditioned_coefficient_support (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I)
    (hne : coefficient (fun f => B (restrictQuery valid f)) s ≠ 0) :
    ∀ i ∈ support s, valid i = true := by
  intro i hi
  have hs := (Finset.mem_filter.mp hi).2
  cases hv : valid i
  · exact False.elim (hne (conditioned_coefficient_zero_invalid valid B s i hv hs))
  · rfl

def conditionedFoldedAnswer (valid : I → Bool) (i₀ : {i : I // valid i = true})
    (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  foldedAnswer i₀ table (restrictQuery valid f)

omit [Fintype I] [DecidableEq I] in
theorem conditionedFoldedAnswer_flip (valid : I → Bool)
    (i₀ : {i : I // valid i = true}) (table : HalfCube i₀ → Bool) (f : Cube I) :
    conditionedFoldedAnswer valid i₀ table (cubeFlip f) =
      !(conditionedFoldedAnswer valid i₀ table f) := by
  change foldedAnswer i₀ table (cubeFlip (restrictQuery valid f)) = _
  exact foldedAnswer_flip i₀ table (restrictQuery valid f)

theorem conditionedFoldedAnswer_zero_coefficient (valid : I → Bool)
    (i₀ : {i : I // valid i = true}) (table : HalfCube i₀ → Bool) :
    coefficient (fun f => bitSign (conditionedFoldedAnswer valid i₀ table f))
      (fun _ => false) = 0 :=
  coefficient_sign_zero_of_folded _ (conditionedFoldedAnswer_flip valid i₀ table)

omit [Fintype I] [DecidableEq I] in
theorem conditionedFoldedAnswer_dictator (valid : I → Bool)
    (i₀ i : {i : I // valid i = true}) (f : Cube I) :
    conditionedFoldedAnswer valid i₀ (fun h => h.val i) f = f i.val := by
  exact foldedAnswer_dictator i₀ i (restrictQuery valid f)

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

/-! The parity projection and finite Fourier decoder used in Håstad's
three-query argument. Probabilities are explicit finite sums. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def parityProjection (π : J → I) (s : Cube J) : Cube I := fun i =>
  decide (Odd ((support s).filter fun y => π y = i).card)

theorem walsh_support (s x : Cube I) :
    walsh s x = ∏ i ∈ support s, bitSign (x i) := by
  unfold walsh support
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [bitSign]

theorem sign_power_parity (b : Bool) (n : Nat) :
    bitSign b ^ n = bitSign (decide (Odd n) && b) := by
  cases b
  · simp [bitSign]
  · simp only [Bool.and_true, bitSign, ite_true, decide_eq_true_eq]
    rw [neg_one_pow_eq_ite]
    by_cases h : Even n
    · simp [h, Nat.not_odd_iff_even.mpr h]
    · simp [h, Nat.not_even_iff_odd.mp h]

theorem walsh_pullback (π : J → I) (s : Cube J) (f : Cube I) :
    walsh s (fun y => f (π y)) = walsh (parityProjection π s) f := by
  rw [walsh_support]
  rw [← Finset.prod_fiberwise' (support s) π (fun i => bitSign (f i))]
  unfold walsh parityProjection
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.prod_const]
  exact sign_power_parity (f i) _

theorem projectedCoefficient_eq (π : J → I) (A : Cube I → ℝ) (s : Cube J) :
    projectedCoefficient π A s = coefficient A (parityProjection π s) := by
  simp only [projectedCoefficient, coefficient, walsh_pullback]

omit [DecidableEq J] in
theorem projection_has_preimage (π : J → I) (s : Cube J) (i : I)
    (hi : i ∈ support (parityProjection π s)) :
    ∃ y ∈ support s, π y = i := by
  have hodd : Odd ((support s).filter fun y => π y = i).card := by
    have hbit := (Finset.mem_filter.mp hi).2
    simpa only [parityProjection, decide_eq_true_eq] using hbit
  have hp : 0 < ((support s).filter fun y => π y = i).card := by
    obtain ⟨n, hn⟩ := hodd
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
  exact ⟨y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩

/-- A purely algebraic decay estimate used instead of exponential bounds. -/
theorem scaled_geometric_power_le_one {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (n : Nat) :
    (n : ℝ) * (1 - t) * t ^ n ≤ 1 := by
  have hsum : (n : ℝ) * t ^ n ≤ ∑ j ∈ Finset.range n, t ^ j := by
    calc
      (n : ℝ) * t ^ n = ∑ _j ∈ Finset.range n, t ^ n := by simp
      _ ≤ ∑ j ∈ Finset.range n, t ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_of_le_one ht ht' (Nat.le_of_lt (Finset.mem_range.mp hj))
  have hm := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr ht')
  rw [geom_sum_mul_neg] at hm
  have hp : 0 ≤ t ^ n := pow_nonneg ht _
  nlinarith

theorem noise_decay_bound {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    {k : Nat} (hk : 0 < k) :
    4 * ε * ((1 - 2 * ε) ^ k) ^ 2 ≤ 1 / (k : ℝ) := by
  have h := scaled_geometric_power_le_one (t := 1 - 2 * ε)
    (by linarith) (by linarith) (2 * k)
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (le_div_iff₀ hkp).mpr
  have hpow : (1 - 2 * ε) ^ (2 * k) = ((1 - 2 * ε) ^ k) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [hpow] at h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

def zeroMask : Cube I := fun _ => false

omit [DecidableEq I] in
theorem support_eq_empty_iff (s : Cube I) : support s = ∅ ↔ s = zeroMask := by
  constructor
  · intro h
    funext i
    have hi : i ∉ support s := by rw [h]; simp
    have : s i ≠ true := by simpa [support] using hi
    cases hs : s i <;> simp_all [zeroMask]
  · intro h
    subst s
    simp [zeroMask, support]

omit [Fintype I] [DecidableEq J] in
theorem parityProjection_zero (π : J → I) :
    parityProjection π (zeroMask : Cube J) = zeroMask := by
  funext i
  simp [parityProjection, support, zeroMask]

/-- Choose uniform coordinates in the two masks and check the projection.
An empty support contributes zero. -/
def agreementProbability (π : J → I) (a : Cube I) (b : Cube J) : ℝ :=
  (∑ i ∈ support a, (((support b).filter fun y => π y = i).card : ℝ)) /
    ((support a).card * (support b).card : ℝ)

omit [DecidableEq J] in
theorem agreementProbability_nonneg (π : J → I) (a : Cube I) (b : Cube J) :
    0 ≤ agreementProbability π a b := by
  unfold agreementProbability
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [DecidableEq J] in
theorem agreementProbability_projection (π : J → I) (b : Cube J)
    (ha : (support (parityProjection π b)).Nonempty) :
    1 / ((support b).card : ℝ) ≤ agreementProbability π (parityProjection π b) b := by
  have hca : (0 : ℝ) < (support (parityProjection π b)).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ha)
  have hb : (support b).Nonempty := by
    obtain ⟨i, hi⟩ := ha
    obtain ⟨y, hy, _⟩ := projection_has_preimage π b i hi
    exact ⟨y, hy⟩
  have hcb : (0 : ℝ) < (support b).card := Nat.cast_pos.mpr (Finset.card_pos.mpr hb)
  have hsum : ((support (parityProjection π b)).card : ℝ) ≤
      ∑ i ∈ support (parityProjection π b),
        (((support b).filter fun y => π y = i).card : ℝ) := by
    calc
      _ = ∑ _i ∈ support (parityProjection π b), (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨y, hy, hπ⟩ := projection_has_preimage π b i hi
        have hp : 0 < ((support b).filter fun y => π y = i).card :=
          Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hπ⟩⟩
        exact_mod_cast hp
  unfold agreementProbability
  apply (div_le_div_iff₀ hcb (mul_pos hca hcb)).mpr
  nlinarith

/-- Select independent Walsh masks by squared coefficients and uniform points
in each support. The two selections use only the respective private tables. -/
def decoderSuccess (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)

def decodingEnergy (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  ∑ b, projectedCoefficient π A b ^ 2 * coefficient B b ^ 2 / (support b).card

theorem decodingEnergy_le_success (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    decodingEnergy π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ≤
      decoderSuccess π A B := by
  unfold decodingEnergy decoderSuccess
  apply Finset.sum_le_sum
  intro b _
  rw [projectedCoefficient_eq]
  have hsum :
      coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        agreementProbability π (parityProjection π b) b ≤
      ∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b := by
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun a => coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)
    · intro a _
      exact mul_nonneg (sq_nonneg _) (agreementProbability_nonneg π a b)
    · exact Finset.mem_univ _
  have hm := mul_le_mul_of_nonneg_left hsum
    (sq_nonneg (coefficient (fun g => bitSign (B g)) b))
  by_cases ha : (support (parityProjection π b)).Nonempty
  · have hagree := agreementProbability_projection π b ha
    have ht := mul_le_mul_of_nonneg_left hagree
      (mul_nonneg (sq_nonneg (coefficient (fun f => bitSign (A f))
        (parityProjection π b))) (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    have heq : coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2 / (support b).card =
      (coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2) * (1 / (support b).card) := by ring
    rw [heq]
    exact ht.trans (by convert hm using 1; ring)
  · have hempty : support (parityProjection π b) = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hz := (support_eq_empty_iff _).mp hempty
    simpa [hz, hzero] using hm

theorem bias_sq_le_weighted_energy (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → Bool) :
    testBias ε π A (fun g => bitSign (B g)) ^ 2 ≤
      ∑ b, (projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
        (1 - 2 * ε) ^ (support b).card) ^ 2 := by
  rw [testBias_fourier]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun b => projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
      (1 - 2 * ε) ^ (support b).card)
    (fun b => coefficient (fun g => bitSign (B g)) b)
  rw [sign_parseval, mul_one] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem decoder_four_epsilon_bias_sq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    4 * ε * testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ^ 2 ≤
      decoderSuccess π A B := by
  apply le_trans _ (decodingEnergy_le_success π A B hzero)
  have hcs := mul_le_mul_of_nonneg_left
    (bias_sq_le_weighted_energy ε π (fun f => bitSign (A f)) B)
    (by linarith : 0 ≤ 4 * ε)
  apply hcs.trans
  rw [Finset.mul_sum]
  unfold decodingEnergy
  apply Finset.sum_le_sum
  intro b _
  by_cases hk : 0 < (support b).card
  · have hd := noise_decay_bound hε hε' hk
    have hm := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (sq_nonneg (projectedCoefficient π (fun f => bitSign (A f)) b))
        (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    convert hm using 1 <;> ring
  · have hb : support b = ∅ := Finset.card_eq_zero.mp (by omega)
    have hbzero := (support_eq_empty_iff b).mp hb
    subst b
    simp [projectedCoefficient_eq, parityProjection_zero, hzero, support, zeroMask]

/-- A concrete folded half-table discharges the zero-coefficient condition. -/
theorem folded_decoder_bound (ε : ℝ) (π : J → I)
    (i₀ : I) (table : HalfCube i₀ → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ table f))
      (fun g => bitSign (B g)) ^ 2 ≤ decoderSuccess π (foldedAnswer i₀ table) B := by
  exact decoder_four_epsilon_bias_sq ε π (foldedAnswer i₀ table) B hε hε'
    (foldedAnswer_zero_coefficient i₀ table)

def validAgreementProbability (valid : J → Bool) (π : J → I)
    (a : Cube I) (b : Cube J) : ℝ :=
  (∑ i ∈ support a,
    (((support b).filter fun y => π y = i ∧ valid y = true).card : ℝ)) /
    ((support a).card * (support b).card : ℝ)

omit [DecidableEq J] in
theorem validAgreementProbability_eq (valid : J → Bool) (π : J → I)
    (a : Cube I) (b : Cube J) (hb : ∀ y ∈ support b, valid y = true) :
    validAgreementProbability valid π a b = agreementProbability π a b := by
  unfold validAgreementProbability agreementProbability
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro y hy
  simp [hb y hy]

def validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 *
      validAgreementProbability valid π a b)

/-- Clause validity in the decoded game follows from the concrete conditioned
table; no Fourier-support hypothesis is passed to this theorem. -/
theorem conditioned_validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (j₀ : {j : J // valid j = true})
    (table : HalfCube j₀ → Bool) :
    validDecoderSuccess valid π A (conditionedFoldedAnswer valid j₀ table) =
      decoderSuccess π A (conditionedFoldedAnswer valid j₀ table) := by
  unfold validDecoderSuccess decoderSuccess
  apply Finset.sum_congr rfl
  intro b _
  by_cases hc : coefficient (fun g => bitSign (conditionedFoldedAnswer valid j₀ table g)) b = 0
  · simp [hc]
  · have hb : ∀ y ∈ support b, valid y = true := by
      apply conditioned_coefficient_support valid (fun g => bitSign (foldedAnswer j₀ table g)) b
      exact hc
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [validAgreementProbability_eq valid π a b hb]

theorem conditioned_folded_decoder_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool)
    (j₀ : {j : J // valid j = true}) (tableB : HalfCube j₀ → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (conditionedFoldedAnswer valid j₀ tableB g)) ^ 2 ≤
      validDecoderSuccess valid π (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) := by
  rw [conditioned_validDecoderSuccess]
  exact folded_decoder_bound ε π i₀ tableA
    (conditionedFoldedAnswer valid j₀ tableB) hε hε'

end UniqueGamesTheorem.Foundations.Hastad

end

end

end OAI
