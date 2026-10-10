import OAI.Analysis.LipschitzHilbert.Phase.FourthMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace OAI

/-!
# The dominant-coefficient case of the finite phase estimate

These are the mean-zero fourth-moment and elementary exponent estimates
in §7, proof of Proposition `phase:finite-fourier`. A quadratic Young
inequality absorbs the cubic cross term before integration.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem finiteFourierSum_bound (frequency : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    ‖finiteFourierSum frequency a t‖ ≤ ∑ i, ‖a i‖ := by
  unfold finiteFourierSum
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_mul, norm_character, mul_one]

theorem continuous_finiteFourierSum (frequency : ι → ℝ) (a : ι → ℂ) :
    Continuous (finiteFourierSum frequency a) := by
  unfold finiteFourierSum
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_character _)

theorem integral_finiteFourierSum (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) :
    (∫ t, finiteFourierSum frequency a t ∂ν) =
      ∑ i, a i * fourierMoment ν (frequency i) := by
  unfold finiteFourierSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_const_mul _ _
  · intro i _
    exact (integrable_character ν _).const_mul _

theorem integral_finiteFourierSum_eq_zero (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap : ℝ} (hν : FourierGap ν gap)
    (hzero : ∀ i, gap / 4 ≤ |frequency i|) :
    (∫ t, finiteFourierSum frequency a t ∂ν) = 0 := by
  rw [integral_finiteFourierSum]
  apply Finset.sum_eq_zero
  intro i _
  rw [hν _ (hzero i), mul_zero]

theorem finiteFourierSum_second_expansion (frequency : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    ((‖finiteFourierSum frequency a t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, (a i * conj (a j)) * character (frequency i - frequency j) t := by
  have hnorm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    intro z
    rw [Complex.mul_conj']
    push_cast
    rfl
  rw [hnorm, finiteFourierSum, map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, character_conj]
  calc
    _ = (a i * conj (a j)) * (character (frequency i) t * character (-frequency j) t) := by ring
    _ = _ := by rw [character_mul]; rfl

theorem integral_finiteFourierSum_second (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 2 ∂ν) = ∑ i, ‖a i‖ ^ 2 := by
  classical
  have hm (i j : ι) : fourierMoment ν (frequency i - frequency j) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simp [fourierMoment, character]
    · simp only [hij, ite_false]
      exact hν _ (le_trans (by linarith) (hsep hij))
  have hexp : (∫ t, ((‖finiteFourierSum frequency a t‖ ^ 2 : ℝ) : ℂ) ∂ν) =
      ∑ i, ∑ j, (a i * conj (a j)) * fourierMoment ν (frequency i - frequency j) := by
    simp_rw [finiteFourierSum_second_expansion]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        exact integral_const_mul _ _
      · intro j _
        exact (integrable_character ν _).const_mul _
    · intro i _
      exact integrable_finsetSum _ fun j _ => (integrable_character ν _).const_mul _
  simp_rw [hm] at hexp
  simp only [mul_ite, mul_one, mul_zero] at hexp
  rw [integral_complex_ofReal] at hexp
  have hre := congrArg Complex.re hexp
  simpa [Complex.mul_conj', ← Complex.ofReal_pow] using hre

omit [Fintype ι] in
theorem one_add_norm_fourth_le (z : ℂ) :
    ‖1 + z‖ ^ 4 ≤ 1 + 4 * z.re + 8 * ‖z‖ ^ 2 + 3 * ‖z‖ ^ 4 := by
  have hs : ‖1 + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add]
    simp [Complex.normSq_eq_norm_sq]
    ring
  have hre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have habs : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [Complex.sq_norm_sub_sq_re z, sq_nonneg z.im]
  have hcross : z.re * ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hre (sq_nonneg ‖z‖)]
  have hyoung : 2 * ‖z‖ ^ 3 ≤ ‖z‖ ^ 2 + ‖z‖ ^ 4 := by
    nlinarith [sq_nonneg (‖z‖ - ‖z‖ ^ 2)]
  have heq : ‖1 + z‖ ^ 4 = (1 + 2 * z.re + ‖z‖ ^ 2) ^ 2 := by
    rw [← hs]
    ring
  rw [heq]
  nlinarith

omit [Fintype ι] in
theorem bounded_norm_power_integrable {ν : Measure ℝ} [IsFiniteMeasure ν]
    {U : ℝ → ℂ} (hU : AEStronglyMeasurable U ν) {B : ℝ}
    (_hB : 0 ≤ B) (hbound : ∀ t, ‖U t‖ ≤ B) (n : ℕ) :
    Integrable (fun t => ‖U t‖ ^ n) ν := by
  apply Integrable.of_bound (hU.norm.pow n) (B ^ n)
  filter_upwards [] with t
  change ‖‖U t‖ ^ n‖ ≤ B ^ n
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) n)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound t) n

omit [Fintype ι] in
theorem bounded_one_add_fourth_integrable {ν : Measure ℝ} [IsFiniteMeasure ν]
    {U : ℝ → ℂ} (hU : AEStronglyMeasurable U ν) {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ t, ‖U t‖ ≤ B) :
    Integrable (fun t => ‖1 + U t‖ ^ 4) ν := by
  apply bounded_norm_power_integrable (aestronglyMeasurable_const.add hU)
    (show 0 ≤ 1 + B by linarith)
  intro t
  calc
    ‖1 + U t‖ ≤ ‖(1 : ℂ)‖ + ‖U t‖ := norm_add_le _ _
    _ ≤ 1 + B := by simpa using add_le_add_left (hbound t) 1

/- The dominant remainder has fourth moment at most `1 + 14 b²`.
The moment assumptions here are the second and fourth moments of the
actual mean-zero remainder, before adding its dominant constant. -/
omit [Fintype ι] in
theorem mean_zero_fourth_moment_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {U : ℝ → ℂ} (hU : AEStronglyMeasurable U ν) {B b : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ t, ‖U t‖ ≤ B)
    (hmean : ∫ t, U t ∂ν = 0) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hsecond : ∫ t, ‖U t‖ ^ 2 ∂ν ≤ b ^ 2)
    (hfourth : ∫ t, ‖U t‖ ^ 4 ∂ν ≤ 2 * b ^ 4) :
    (∫ t, ‖1 + U t‖ ^ 4 ∂ν) ≤ 1 + 14 * b ^ 2 := by
  have hiU : Integrable U ν :=
    Integrable.of_bound hU B (Filter.Eventually.of_forall hbound)
  have hi2 := bounded_norm_power_integrable hU hB hbound 2
  have hi4 := bounded_norm_power_integrable hU hB hbound 4
  have hiplus := bounded_one_add_fourth_integrable hU hB hbound
  have hire : Integrable (fun t => (U t).re) ν := hiU.re
  have himean : ∫ t, (U t).re ∂ν = 0 := by
    have heq := integral_re hiU
    change (∫ t, (U t).re ∂ν) = (∫ t, U t ∂ν).re at heq
    rw [heq, hmean]
    rfl
  have hle : (∫ t, ‖1 + U t‖ ^ 4 ∂ν) ≤
      1 + 8 * (∫ t, ‖U t‖ ^ 2 ∂ν) + 3 * (∫ t, ‖U t‖ ^ 4 ∂ν) := by
    calc
      _ ≤ ∫ t, (1 + 4 * (U t).re + 8 * ‖U t‖ ^ 2 + 3 * ‖U t‖ ^ 4) ∂ν :=
        integral_mono hiplus
          (((integrable_const 1).add (hire.const_mul 4)).add (hi2.const_mul 8) |>.add
            (hi4.const_mul 3)) (fun t => one_add_norm_fourth_le (U t))
      _ = _ := by
        rw [integral_add (f := fun t => 1 + 4 * (U t).re + 8 * ‖U t‖ ^ 2)
          (((integrable_const 1).add (hire.const_mul 4)).add (hi2.const_mul 8))
          (hi4.const_mul 3), integral_add (f := fun t => 1 + 4 * (U t).re)
          ((integrable_const 1).add (hire.const_mul 4)) (hi2.const_mul 8),
          integral_add (f := fun _ => 1) (integrable_const 1) (hire.const_mul 4)]
        simp [integral_const_mul, himean]
  have hb4 : b ^ 4 ≤ b ^ 2 := by
    nlinarith [sq_nonneg b, mul_self_le_mul_self hb hb1,
      sq_nonneg (b ^ 2 - 1)]
  nlinarith

/- The numerical comparison in the dominant case, including the
constant-one convexity step. -/
omit [Fintype ι] in
theorem dominant_exponent_bound {b r : ℝ} (hb : 0 ≤ b) (hsmall : b ≤ 1 / 64)
    (hr : 0 < r) (hrupper : r ≤ 3 / 2) :
    1 + 14 * b ^ 2 ≤ (1 + b ^ r) ^ (4 / r) := by
  have hb1 : b ≤ 1 := by linarith
  have hpow : b ^ (2 - r) ≤ 1 / 8 := by
    calc
      b ^ (2 - r) ≤ b ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' hb hb1 (by norm_num) (by linarith)
      _ = Real.sqrt b := (Real.sqrt_eq_rpow b).symm
      _ ≤ 1 / 8 := by
        apply (Real.sqrt_le_iff).2
        constructor <;> nlinarith
  have hfactor : b ^ 2 = b ^ r * b ^ (2 - r) := by
    rw [← Real.rpow_add' hb (by linarith : r + (2 - r) ≠ 0)]
    norm_num
  have hlinear : 14 * b ^ 2 ≤ (8 / 3) * b ^ r := by
    rw [hfactor]
    nlinarith [mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hb r)]
  have hexponent : (8 / 3 : ℝ) ≤ 4 / r := by
    apply (le_div_iff₀ hr).2
    nlinarith
  calc
    1 + 14 * b ^ 2 ≤ 1 + (8 / 3) * b ^ r := by linarith
    _ ≤ 1 + (4 / r) * b ^ r :=
      add_le_add_right (mul_le_mul_of_nonneg_right hexponent (Real.rpow_nonneg hb r)) 1
    _ ≤ _ := one_add_mul_self_le_rpow_one_add
      (by linarith [Real.rpow_nonneg hb r]) (by linarith)

omit [Fintype ι] in
theorem dominant_fourth_moment_bound {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {U : ℝ → ℂ} (hU : AEStronglyMeasurable U ν) {B b r : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ t, ‖U t‖ ≤ B)
    (hmean : ∫ t, U t ∂ν = 0) (hb : 0 ≤ b) (hsmall : b ≤ 1 / 64)
    (hr : 0 < r) (hrupper : r ≤ 3 / 2)
    (hsecond : ∫ t, ‖U t‖ ^ 2 ∂ν ≤ b ^ 2)
    (hfourth : ∫ t, ‖U t‖ ^ 4 ∂ν ≤ 2 * b ^ 4) :
    (∫ t, ‖1 + U t‖ ^ 4 ∂ν) ≤ (1 + b ^ r) ^ (4 / r) :=
  (mean_zero_fourth_moment_le hU hB hbound hmean hb (by linarith) hsecond hfourth).trans
    (dominant_exponent_bound hb hsmall hr hrupper)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
