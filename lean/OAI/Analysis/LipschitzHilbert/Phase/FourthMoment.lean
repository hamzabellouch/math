import OAI.Analysis.LipschitzHilbert.Phase.QuantileGap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace OAI

/-!
# Fourth moments of separated finite Fourier sums

The exact finite expansion and Fourier-support reduction used in §7,
proof of Proposition `phase:finite-fourier`. The annihilation hypothesis
is a property of the averaging probability measure, not a new axiom.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

def character (frequency t : ℝ) : ℂ := Complex.exp ((frequency * t : ℝ) * Complex.I)

theorem norm_character (frequency t : ℝ) : ‖character frequency t‖ = 1 := by
  simp [character, Complex.norm_exp]

theorem character_mul (a b t : ℝ) : character a t * character b t = character (a + b) t := by
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem character_conj (a t : ℝ) : conj (character a t) = character (-a) t := by
  unfold character
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem character_four (a b c d t : ℝ) :
    character a t * character b t * conj (character c t) * conj (character d t) =
      character (a + b - c - d) t := by
  rw [character_conj, character_conj, character_mul, character_mul, character_mul]
  congr 1

theorem continuous_character (a : ℝ) : Continuous (character a) := by
  unfold character
  fun_prop

theorem integrable_character (ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ) :
    Integrable (character a) ν :=
  Integrable.of_bound (continuous_character a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun t => (norm_character a t).le)

def finiteFourierSum (frequency : ι → ℝ) (coefficient : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i, coefficient i * character (frequency i) t

theorem sum_four_product (a b c d : ι → ℂ) :
    (∑ q : Quadruple ι, a q.1 * b q.2.1 * c q.2.2.1 * d q.2.2.2) =
      (∑ i, a i) * (∑ j, b j) * (∑ k, c k) * (∑ l, d l) := by
  simp only [Fintype.sum_prod_type]
  have hthree : (∑ i, a i) * (∑ j, b j) * (∑ k, c k) =
      ∑ i, ∑ j, ∑ k, a i * b j * c k := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
  symm
  rw [hthree]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem norm_fourth_as_product (z : ℂ) :
    ((‖z‖ ^ 4 : ℝ) : ℂ) = z * z * conj z * conj z := by
  calc
    _ = (z * conj z) ^ 2 := by
      rw [Complex.mul_conj']
      push_cast
      ring
    _ = _ := by ring

theorem fourth_power_sum_expansion (a : ι → ℂ) :
    ((‖∑ i, a i‖ ^ 4 : ℝ) : ℂ) =
      ∑ q : Quadruple ι, a q.1 * a q.2.1 * conj (a q.2.2.1) * conj (a q.2.2.2) := by
  rw [sum_four_product a a (fun i => conj (a i)) (fun i => conj (a i))]
  have hc : (∑ i, conj (a i)) = conj (∑ i, a i) :=
    (map_sum (starRingEnd ℂ) a Finset.univ).symm
  rw [hc]
  exact norm_fourth_as_product _

def coefficientProduct (a : ι → ℂ) (q : Quadruple ι) : ℂ :=
  a q.1 * a q.2.1 * conj (a q.2.2.1) * conj (a q.2.2.2)

def frequencyDifference (frequency : ι → ℝ) (q : Quadruple ι) : ℝ :=
  frequency q.1 + frequency q.2.1 - frequency q.2.2.1 - frequency q.2.2.2

/-- Exact fourth-power expansion with all cross terms retained. -/
theorem finiteFourierSum_fourth_expansion (frequency : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    ((‖finiteFourierSum frequency a t‖ ^ 4 : ℝ) : ℂ) =
      ∑ q : Quadruple ι, coefficientProduct a q * character (frequencyDifference frequency q) t := by
  rw [finiteFourierSum, fourth_power_sum_expansion]
  apply Finset.sum_congr rfl
  intro q _
  rcases q with ⟨i, j, k, l⟩
  dsimp only [coefficientProduct, frequencyDifference]
  calc
    _ = (a i * a j * conj (a k) * conj (a l)) *
        (character (frequency i) t * character (frequency j) t *
          conj (character (frequency k) t) * conj (character (frequency l) t)) := by
      simp only [map_mul]
      ring
    _ = _ := by rw [character_four]

theorem integrable_fourth_power (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) :
    Integrable (fun t => ‖finiteFourierSum frequency a t‖ ^ 4) ν := by
  have hs : Integrable (fun t => ∑ q : Quadruple ι,
      coefficientProduct a q * character (frequencyDifference frequency q) t) ν :=
    integrable_finsetSum Finset.univ fun q _ => (integrable_character ν _).const_mul _
  have hc : Integrable (fun t => ((‖finiteFourierSum frequency a t‖ ^ 4 : ℝ) : ℂ)) ν :=
    hs.congr (Filter.Eventually.of_forall fun t => (finiteFourierSum_fourth_expansion frequency a t).symm)
  convert hc.re using 1

def fourierMoment (ν : Measure ℝ) (s : ℝ) : ℂ := ∫ t, character s t ∂ν

theorem norm_fourierMoment_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) :
    ‖fourierMoment ν s‖ ≤ 1 := by
  calc
    ‖fourierMoment ν s‖ ≤ ∫ t, ‖character s t‖ ∂ν := norm_integral_le_integral_norm _
    _ = 1 := by simp [norm_character]

/-- The integral of the finite expansion is the finite sum of Fourier moments. -/
theorem integral_fourth_expansion (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) :
    (∫ t, ((‖finiteFourierSum frequency a t‖ ^ 4 : ℝ) : ℂ) ∂ν) =
      ∑ q : Quadruple ι, coefficientProduct a q * fourierMoment ν (frequencyDifference frequency q) := by
  simp_rw [finiteFourierSum_fourth_expansion]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q _
    exact integral_const_mul _ _
  · intro q _
    exact (integrable_character ν _).const_mul _

/-- A measure with Fourier support in the open interval `(-gap/4,gap/4)`
annihilates all the moments specified in this condition. -/
def FourierGap (ν : Measure ℝ) (gap : ℝ) : Prop :=
  ∀ s : ℝ, gap / 4 ≤ |s| → fourierMoment ν s = 0

theorem fourth_moment_le_resonant_sum (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap : ℝ} (hν : FourierGap ν gap) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      ∑ q : Quadruple ι,
        if Resonant frequency gap q.1 q.2.1 q.2.2.1 q.2.2.2 then
          ‖a q.1‖ * ‖a q.2.1‖ * ‖a q.2.2.1‖ * ‖a q.2.2.2‖ else 0 := by
  classical
  have hexp := integral_fourth_expansion ν frequency a
  have hre : (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) =
      (∑ q : Quadruple ι,
        coefficientProduct a q * fourierMoment ν (frequencyDifference frequency q)).re := by
    rw [integral_complex_ofReal] at hexp
    exact congrArg Complex.re hexp
  rw [hre]
  calc
    _ ≤ ‖∑ q : Quadruple ι,
        coefficientProduct a q * fourierMoment ν (frequencyDifference frequency q)‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ q : Quadruple ι,
        ‖coefficientProduct a q * fourierMoment ν (frequencyDifference frequency q)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _
      by_cases hr : Resonant frequency gap q.1 q.2.1 q.2.2.1 q.2.2.2
      · simp only [hr, ite_true, norm_mul, coefficientProduct, Complex.norm_conj]
        exact mul_le_of_le_one_right (by positivity) (norm_fourierMoment_le_one ν _)
      · have hz : fourierMoment ν (frequencyDifference frequency q) = 0 :=
          hν _ (le_of_not_gt hr)
        simp [hr, hz]

/- The exponent conversion that identifies coefficient products with the
probability weights in the quantile argument. -/
omit [Fintype ι] in
theorem norm_product_eq_weight_rpow (a : ι → ℂ) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hnorm : ∀ i, ‖a i‖ = x i ^ (3 / 4 : ℝ))
    (i j k l : ι) :
    ‖a i‖ * ‖a j‖ * ‖a k‖ * ‖a l‖ =
      (x i * x j * x k * x l) ^ (3 / 4 : ℝ) := by
  rw [hnorm i, hnorm j, hnorm k, hnorm l]
  rw [Real.mul_rpow (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k)) (hx l),
    Real.mul_rpow (mul_nonneg (hx i) (hx j)) (hx k), Real.mul_rpow (hx i) (hx j)]

theorem fourth_moment_le_resonanceSum (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) (x : ι → ℝ) {gap : ℝ}
    (hν : FourierGap ν gap) (hx : ∀ i, 0 ≤ x i)
    (hnorm : ∀ i, ‖a i‖ = x i ^ (3 / 4 : ℝ)) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤ resonanceSum frequency gap x := by
  refine (fourth_moment_le_resonant_sum ν frequency a hν).trans_eq ?_
  apply Finset.sum_congr rfl
  intro q _
  rcases q with ⟨i, j, k, l⟩
  rw [geometricTerm_eq_rpow hx]
  split_ifs
  · exact norm_product_eq_weight_rpow a x hx hnorm i j k l
  · rfl

def coefficientMass (a : ι → ℂ) (i : ι) : ℝ := ‖a i‖ ^ (4 / 3 : ℝ)

omit [Fintype ι] in
theorem coefficientMass_nonneg (a : ι → ℂ) (i : ι) : 0 ≤ coefficientMass a i :=
  Real.rpow_nonneg (norm_nonneg _) _

omit [Fintype ι] in
theorem coefficientMass_rpow (a : ι → ℂ) (i : ι) :
    coefficientMass a i ^ (3 / 4 : ℝ) = ‖a i‖ := by
  unfold coefficientMass
  rw [← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-- The ordinary constant-one fourth-moment estimate at unit `ℓ^(4/3)` norm. -/
theorem normalized_fourth_moment_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hunit : ∑ i, coefficientMass a i = 1) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤ 1 :=
  (fourth_moment_le_resonanceSum ν frequency a (coefficientMass a) hν
    (coefficientMass_nonneg a) (fun i => (coefficientMass_rpow a i).symm)).trans
    (resonanceSum_le_one hgap hsep (coefficientMass a) (coefficientMass_nonneg a) hunit)

/-- The strict quantitative fourth-moment gap when no coefficient carries
almost all of the normalized `ℓ^(4/3)` mass. -/
theorem normalized_fourth_moment_quantile_gap (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hunit : ∑ i, coefficientMass a i = 1)
    (hatom : ∀ i, coefficientMass a i ≤ 1 - κ) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096 :=
  (fourth_moment_le_resonanceSum ν frequency a (coefficientMass a) hν
    (coefficientMass_nonneg a) (fun i => (coefficientMass_rpow a i).symm)).trans
    (quantile_gap hgap hsep hκ hκ1 (coefficientMass a)
      (coefficientMass_nonneg a) hunit hatom)

theorem normalized_fourth_moment_quantile_gap_simplified
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hunit : ∑ i, coefficientMass a i = 1)
    (hatom : ∀ i, coefficientMass a i ≤ 1 - κ) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤ 1 - κ ^ 4 / 16384 :=
  (fourth_moment_le_resonanceSum ν frequency a (coefficientMass a) hν
    (coefficientMass_nonneg a) (fun i => (coefficientMass_rpow a i).symm)).trans
    (quantile_gap_simplified hgap hsep hκ hκ1 (coefficientMass a)
      (coefficientMass_nonneg a) hunit hatom)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
