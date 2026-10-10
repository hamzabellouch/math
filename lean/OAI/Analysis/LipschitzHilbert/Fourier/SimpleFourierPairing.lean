import OAI.Analysis.LipschitzHilbert.Phase.FiniteInterpolation
import OAI.Analysis.LipschitzHilbert.Phase.ImprovedFourthMoment
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-!
# Simple tests for Fourier interpolation on the actual averaging measure

A finite measurable profile partitions the real line into its fibers.
Its matrix entries are actual Fourier integrals over those fibers. The
two finite interpolation endpoints follow from positivity and the proved
improved fourth-moment theorem.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
theorem profile_eq_sum {E : Type*} [AddCommMonoid E] (φ : ℝ → κ) (b : κ → E) (t : ℝ) :
    b (φ t) = ∑ j, ({u | φ u = j}.indicator (fun _ => b j)) t := by
  classical
  symm
  calc
    _ = ({u | φ u = φ t}.indicator (fun _ => b (φ t))) t := by
      apply Finset.sum_eq_single (φ t)
      · intro j _ hj
        exact Set.indicator_of_notMem (fun h => hj h.symm) _
      · simp
    _ = _ := by simp

omit [Fintype ι] in
theorem integrable_profile (ν : Measure ℝ) [IsFiniteMeasure ν]
    (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j}) (b : κ → ℂ) :
    Integrable (fun t => b (φ t)) ν := by
  have heq : (fun t => b (φ t)) = fun t => ∑ j, ({u | φ u = j}.indicator (fun _ => b j)) t := by
    funext t
    exact profile_eq_sum φ b t
  rw [heq]
  exact integrable_finsetSum _ fun j _ => (integrable_const _).indicator (hφ j)

omit [Fintype ι] in
theorem profile_bound (φ : ℝ → κ) (b : κ → ℂ) (t : ℝ) :
    ‖b (φ t)‖ ≤ ∑ j, ‖b j‖ :=
  Finset.single_le_sum (fun j _ => norm_nonneg (b j)) (Finset.mem_univ _)

omit [Fintype ι] in
theorem integral_profile_power (ν : Measure ℝ) [IsFiniteMeasure ν]
    (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j}) (b : κ → ℂ) (p : ℝ) :
    (∫ t, ‖b (φ t)‖ ^ p ∂ν) = ∑ j, ν.real {t | φ t = j} * ‖b j‖ ^ p := by
  have heq : (fun t => ‖b (φ t)‖ ^ p) =
      fun t => ∑ j, ({u | φ u = j}.indicator (fun _ => ‖b j‖ ^ p)) t := by
    funext t
    exact profile_eq_sum φ (fun j => ‖b j‖ ^ p) t
  rw [heq, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    simpa only [smul_eq_mul] using integral_indicator_const (μ := ν) (‖b j‖ ^ p) (hφ j)
  · intro j _
    exact (integrable_const _).indicator (hφ j)

def profileMatrix (ν : Measure ℝ) (frequency : ι → ℝ) (φ : ℝ → κ) (i : ι) (j : κ) : ℂ :=
  ∫ t in {u | φ u = j}, character (frequency i) t ∂ν

omit [Fintype ι] [Fintype κ] in
theorem norm_profileMatrix_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (φ : ℝ → κ) (i : ι) (j : κ) :
    ‖profileMatrix ν frequency φ i j‖ ≤ ν.real {u | φ u = j} := by
  calc
    _ ≤ ∫ t in {u | φ u = j}, ‖character (frequency i) t‖ ∂ν := norm_integral_le_integral_norm _
    _ = _ := by simp [norm_character, Measure.real]

theorem finitePairing_profileMatrix (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j})
    (a : ι → ℂ) (b : κ → ℂ) :
    finitePairing (profileMatrix ν frequency φ) a b =
      ∫ t, finiteFourierSum frequency a t * b (φ t) ∂ν := by
  have hpoint (t : ℝ) : finiteFourierSum frequency a t * b (φ t) =
      ∑ i, ∑ j, (a i * b j) * ({u | φ u = j}.indicator (character (frequency i))) t := by
    rw [finiteFourierSum, profile_eq_sum φ b t, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases ht : φ t = j
    · simp only [Set.indicator, Set.mem_ofPred_eq, ht, ite_true]
      ring
    · simp only [Set.indicator, Set.mem_ofPred_eq, ht, ite_false, mul_zero]
  have hint (i : ι) (j : κ) : Integrable
      (fun t => (a i * b j) * ({u | φ u = j}.indicator (character (frequency i))) t) ν :=
    ((integrable_character ν _).indicator (hφ j)).const_mul _
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · unfold finitePairing
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_indicator (hφ j)]
      unfold profileMatrix
      ring
    · intro j _
      exact hint i j
  · intro i _
    exact integrable_finsetSum _ (fun j _ => hint i j)

theorem profileMatrix_fourth_endpoint (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j})
    {gap D : ℝ} (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (a : ι → ℂ) (b : κ → ℂ)
    (ha : (∑ i, ‖a i‖ ^ fourthExponent D) = 1)
    (hb : (∑ j, ν.real {t | φ t = j} * ‖b j‖ ^ (4 / 3 : ℝ)) = 1) :
    ‖finitePairing (profileMatrix ν frequency φ) a b‖ ≤ 1 := by
  have hf : MemLp (finiteFourierSum frequency a) (ENNReal.ofReal 4) ν :=
    MemLp.of_bound (continuous_finiteFourierSum frequency a).aestronglyMeasurable
      (∑ i, ‖a i‖) (Filter.Eventually.of_forall (finiteFourierSum_bound frequency a))
  have hg : MemLp (fun t => b (φ t)) (ENNReal.ofReal (4 / 3 : ℝ)) ν :=
    MemLp.of_bound (integrable_profile ν φ hφ b).aestronglyMeasurable
      (∑ j, ‖b j‖) (Filter.Eventually.of_forall (profile_bound φ b))
  have hpq : (4 : ℝ).HolderConjugate (4 / 3) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hfour := finite_fourier_l4_gain ν frequency a hgap hsep hν hD hcard
  have hfour' : (∫ t, ‖finiteFourierSum frequency a t‖ ^ (4 : ℝ) ∂ν) ^ (1 / 4 : ℝ) ≤ 1 := by
    simpa [sequenceNorm, ha] using hfour
  rw [finitePairing_profileMatrix ν frequency φ hφ a b]
  calc
    _ ≤ ∫ t, ‖finiteFourierSum frequency a t * b (φ t)‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ t, ‖finiteFourierSum frequency a t‖ * ‖b (φ t)‖ ∂ν := by simp only [norm_mul]
    _ ≤ (∫ t, ‖finiteFourierSum frequency a t‖ ^ (4 : ℝ) ∂ν) ^ (1 / 4 : ℝ) *
        (∫ t, ‖b (φ t)‖ ^ (4 / 3 : ℝ) ∂ν) ^ (1 / (4 / 3) : ℝ) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hf hg
    _ ≤ 1 := by
      rw [integral_profile_power ν φ hφ b, hb, Real.one_rpow, mul_one]
      exact hfour'

/-- Arbitrary finite-valued measurable tests, without any normalization on
the test. This is the simple-test input to the bounded duality argument. -/
theorem simple_fourier_pairing_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j})
    {gap D r s t : ℝ} (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hr : 0 < r) (hs : 0 < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrdef : (1 - t) * (r / 1) + t * (r / fourthExponent D) = 1)
    (hsdef : (1 - t) * (s / 1) + t * (s / (4 / 3)) = 1)
    (a : ι → ℂ) (b : κ → ℂ) (ha : (∑ i, ‖a i‖ ^ r) = 1) :
    ‖∫ u, finiteFourierSum frequency a u * b (φ u) ∂ν‖ ≤
      (∫ u, ‖b (φ u)‖ ^ s ∂ν) ^ (1 / s) := by
  have hθ := phaseParameter_range hD
  have hr₄ : 0 < fourthExponent D := by
    apply div_pos (by norm_num : (0 : ℝ) < 4)
    change 0 < 3 - phaseConstant / Real.log (2 * D)
    linarith [hθ.2]
  rw [← finitePairing_profileMatrix ν frequency φ hφ a b,
    integral_profile_power ν φ hφ b]
  apply finite_pairing_interpolation_test (profileMatrix ν frequency φ)
    (fun j => ν.real {u | φ u = j}) (fun j => measureReal_nonneg) (norm_profileMatrix_le ν frequency φ)
    hr hs hr₄ ht0 ht1 hrdef hsdef _ a b ha
  exact profileMatrix_fourth_endpoint ν frequency φ hφ hgap hsep hν hD hcard

omit [Fintype κ] in
theorem simpleFunc_fourier_pairing_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) {gap D r s t : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hr : 0 < r) (hs : 0 < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrdef : (1 - t) * (r / 1) + t * (r / fourthExponent D) = 1)
    (hsdef : (1 - t) * (s / 1) + t * (s / (4 / 3)) = 1)
    (a : ι → ℂ) (g : SimpleFunc ℝ ℂ) (ha : (∑ i, ‖a i‖ ^ r) = 1) :
    ‖∫ u, finiteFourierSum frequency a u * g u ∂ν‖ ≤
      (∫ u, ‖g u‖ ^ s ∂ν) ^ (1 / s) := by
  let φ : ℝ → ↥g.range := fun u => ⟨g u, g.mem_range_self u⟩
  have hφ (j : ↥g.range) : MeasurableSet {u | φ u = j} := by
    convert g.measurableSet_fiber j.val using 1
    ext u
    exact Subtype.ext_iff
  exact simple_fourier_pairing_bound ν frequency φ hφ hgap hsep hν hD hcard
    hr hs ht0 ht1 hrdef hsdef a (fun j => (j : ℂ)) ha

def fourierInterpolationExponent (D p : ℝ) : ℝ :=
  1 / (1 - (1 + phaseParameter D) / p)

omit [Fintype ι] [Fintype κ] in
theorem fourier_interpolation_parameters {D p : ℝ} (hD : 1 ≤ D) (hp : 4 ≤ p) :
    0 < fourierInterpolationExponent D p ∧ 0 < p / (p - 1) ∧
    0 ≤ 4 / p ∧ 4 / p ≤ 1 ∧
    (1 - 4 / p) * (fourierInterpolationExponent D p / 1) +
      (4 / p) * (fourierInterpolationExponent D p / fourthExponent D) = 1 ∧
    (1 - 4 / p) * ((p / (p - 1)) / 1) +
      (4 / p) * ((p / (p - 1)) / (4 / 3)) = 1 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hθ := phaseParameter_range hD
  have hθ' : phaseParameter D ≤ 1 / 3 := hθ.2
  have hq : (1 + phaseParameter D) / p ≤ 1 / 3 :=
    (div_le_iff₀ hp0).2 (by linarith)
  have hd : 0 < 1 - (1 + phaseParameter D) / p := by linarith
  have hdiv : fourierInterpolationExponent D p / fourthExponent D =
      fourierInterpolationExponent D p * (3 - phaseParameter D) / 4 := by
    unfold fourthExponent
    rw [div_div_eq_mul_div]
  refine ⟨one_div_pos.mpr hd, div_pos hp0 hp1, div_nonneg (by norm_num) hp0.le,
    (div_le_one hp0).2 hp, ?_, ?_⟩
  · rw [div_one, hdiv]
    calc
      _ = fourierInterpolationExponent D p * (1 - (1 + phaseParameter D) / p) := by
        field_simp
        ring
      _ = 1 := one_div_mul_cancel hd.ne'
  · field_simp
    ring

omit [Fintype κ] in
theorem simpleFunc_fourier_pairing_bound_at_p (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hp : 4 ≤ p)
    (a : ι → ℂ) (g : SimpleFunc ℝ ℂ)
    (ha : (∑ i, ‖a i‖ ^ fourierInterpolationExponent D p) = 1) :
    ‖∫ u, finiteFourierSum frequency a u * g u ∂ν‖ ≤
      (∫ u, ‖g u‖ ^ (p / (p - 1)) ∂ν) ^ (1 / (p / (p - 1))) := by
  obtain ⟨hr, hs, ht0, ht1, hrdef, hsdef⟩ := fourier_interpolation_parameters hD hp
  exact simpleFunc_fourier_pairing_bound ν frequency hgap hsep hν hD hcard
    hr hs ht0 ht1 hrdef hsdef a g ha

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
