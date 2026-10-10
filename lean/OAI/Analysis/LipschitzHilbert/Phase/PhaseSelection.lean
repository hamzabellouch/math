import OAI.Analysis.LipschitzHilbert.Phase.FiniteFourierGain
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace OAI

/-!
# Averaging separated selections

Finite probability laws on retained subsets and the scalar weighted
phase bound from §9, using the retention cancellation of §8.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable (Ω ι : Type*) [Fintype Ω] [Fintype ι]

/-- Finite probability coordinates and their retained subsets. -/
structure FiniteSelectionLaw where
  weight : Ω → ℝ
  nonnegative : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1
  retained : Ω → Finset ι

variable {Ω ι}

namespace FiniteSelectionLaw

/-- The probability measure represented by the finite coordinates. -/
def measure [MeasurableSpace Ω] (L : FiniteSelectionLaw Ω ι) : Measure Ω :=
  ∑ ω, ENNReal.ofReal (L.weight ω) • Measure.dirac ω

omit [Fintype ι] in
theorem measure_isProbability [MeasurableSpace Ω] (L : FiniteSelectionLaw Ω ι) :
    IsProbabilityMeasure L.measure := by
  constructor
  unfold measure
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => L.nonnegative ω), L.total, ENNReal.ofReal_one]

def marginal (L : FiniteSelectionLaw Ω ι) (i : ι) : ℝ :=
  ∑ ω, if i ∈ L.retained ω then L.weight ω else 0

omit [Fintype ι] in
theorem marginal_nonnegative (L : FiniteSelectionLaw Ω ι) (i : ι) : 0 ≤ L.marginal i := by
  unfold marginal
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact L.nonnegative ω
  · rfl

omit [Fintype ι] in
theorem marginal_le_one (L : FiniteSelectionLaw Ω ι) (i : ι) : L.marginal i ≤ 1 := by
  rw [← L.total]
  apply Finset.sum_le_sum
  intro ω _
  split_ifs
  · exact le_rfl
  · exact L.nonnegative ω

def selectedCoefficient (L : FiniteSelectionLaw Ω ι) (a : ι → ℂ) (ω : Ω) (i : ι) : ℂ :=
  if i ∈ L.retained ω then a i / (L.marginal i : ℂ) else 0

omit [Fintype ι] in
theorem expected_selectedCoefficient (L : FiniteSelectionLaw Ω ι)
    (hπ : ∀ i, L.marginal i ≠ 0) (a : ι → ℂ) (i : ι) :
    (∑ ω, (L.weight ω : ℂ) * L.selectedCoefficient a ω i) = a i := by
  have hsum : (∑ ω, (L.weight ω : ℂ) * L.selectedCoefficient a ω i) =
      (L.marginal i : ℂ) * (a i / (L.marginal i : ℂ)) := by
    unfold selectedCoefficient marginal
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  rw [hsum]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hπ i))

theorem expected_selectedFourier (L : FiniteSelectionLaw Ω ι)
    (hπ : ∀ i, L.marginal i ≠ 0) (frequency : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    (∑ ω, (L.weight ω : ℂ) * finiteFourierSum frequency (L.selectedCoefficient a ω) t) =
      finiteFourierSum frequency a t := by
  unfold finiteFourierSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← mul_assoc, ← Finset.sum_mul, L.expected_selectedCoefficient hπ a i]

theorem selected_cost_expectation (L : FiniteSelectionLaw Ω ι) (a : ι → ℂ) {r : ℝ}
    (hr : 0 < r) (hπ : ∀ i, 0 < L.marginal i) :
    (∑ ω, L.weight ω * ∑ i, ‖L.selectedCoefficient a ω i‖ ^ r) =
      ∑ i, L.marginal i * (‖a i‖ / L.marginal i) ^ r := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [marginal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  unfold selectedCoefficient
  split_ifs
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hπ i)]
    rfl
  · simp [Real.zero_rpow hr.ne']

end FiniteSelectionLaw

theorem sum_subset_indicator {α E : Type*} [Fintype α] [AddCommMonoid E]
    (S : Finset α) (f : α → E) :
    (∑ i, if i ∈ S then f i else 0) = ∑ i : S, f i := by
  classical
  rw [← Finset.sum_filter]
  simpa using (Finset.sum_coe_sort S f).symm

theorem selectedFourier_eq_subtype (L : FiniteSelectionLaw Ω ι)
    (frequency : ι → ℝ) (a : ι → ℂ) (ω : Ω) (t : ℝ) :
    finiteFourierSum frequency (L.selectedCoefficient a ω) t =
      finiteFourierSum (fun i : L.retained ω => frequency i)
        (fun i : L.retained ω => a i / (L.marginal i : ℂ)) t := by
  unfold finiteFourierSum FiniteSelectionLaw.selectedCoefficient
  simp only [ite_mul, zero_mul]
  exact sum_subset_indicator _ _

omit [Fintype ι] in
theorem selection_jensen (L : FiniteSelectionLaw Ω ι) (C : Ω → ℝ)
    (hC : ∀ ω, 0 ≤ C ω) {r : ℝ} (hr : 1 ≤ r) :
    (∑ ω, L.weight ω * C ω ^ (1 / r)) ≤ (∑ ω, L.weight ω * C ω) ^ (1 / r) := by
  have hr0 : 0 < r := by linarith
  have h := (Real.concaveOn_rpow (show 0 ≤ 1 / r by positivity)
    ((div_le_one hr0).2 hr)).le_map_sum (t := Finset.univ)
    (fun ω _ => L.nonnegative ω) L.total (fun ω _ => hC ω)
  simpa only [smul_eq_mul] using h

theorem retention_cancellation {π q μ r : ℝ} (hπ : 0 < π) (hq : 0 < q)
    (hqπ : q ≤ π) (hr : 1 ≤ r) (hrelation : μ * r = r - 1) :
    π ^ (1 - r) * (q ^ μ) ^ r ≤ 1 := by
  rw [← Real.rpow_mul hq.le, hrelation]
  have heq : π ^ (1 - r) * q ^ (r - 1) = (q / π) ^ (r - 1) := by
    rw [Real.div_rpow hq.le hπ.le, div_eq_mul_inv, ← Real.rpow_neg hπ.le]
    have he : 1 - r = -(r - 1) := by ring
    rw [he, mul_comm]
  rw [heq]
  exact Real.rpow_le_one (div_nonneg hq.le hπ.le) ((div_le_one hπ).2 hqπ) (by linarith)

theorem weighted_power_mean (l x : ι → ℝ) (hl : ∀ i, 0 ≤ l i) (hx : ∀ i, 0 ≤ x i)
    (htotal : ∑ i, l i ≤ 1) {r p : ℝ} (hr : 0 < r) (hrp : r ≤ p) :
    (∑ i, l i * x i ^ r) ^ (1 / r) ≤ (∑ i, l i * x i ^ p) ^ (1 / p) := by
  have hp : 0 < p := hr.trans_le hrp
  let w : Option ι → ℝ := fun i => match i with
    | none => 1 - ∑ j, l j
    | some j => l j
  let y : Option ι → ℝ := fun i => match i with
    | none => 0
    | some j => x j ^ p
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    cases i
    · exact sub_nonneg.mpr htotal
    · exact hl _
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    cases i
    · rfl
    · exact Real.rpow_nonneg (hx _) _
  have hsum : ∑ i, w i = 1 := by simp [w]
  have hj := (Real.concaveOn_rpow (div_nonneg hr.le hp.le)
    ((div_le_one hp).2 hrp)).le_map_sum (t := Finset.univ)
    (fun i _ => hw i) hsum (fun i _ => hy i)
  have hpow (i : ι) : (x i ^ p) ^ (r / p) = x i ^ r := by
    rw [← Real.rpow_mul (hx i)]
    congr 1
    field_simp
  have hmean : (∑ i, l i * x i ^ r) ≤ (∑ i, l i * x i ^ p) ^ (r / p) := by
    simpa [w, y, smul_eq_mul, Real.zero_rpow (div_pos hr hp).ne', hpow] using hj
  have hout := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (hx i) _)) hmean
    (show 0 ≤ 1 / r by positivity)
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (hx i) _))] at hout
  have heq : (r / p) * (1 / r) = 1 / p := by field_simp
  simpa only [heq] using hout

theorem selected_power_sum_eq_subtype (L : FiniteSelectionLaw Ω ι) (a : ι → ℂ)
    {r : ℝ} (hr : 0 < r) (ω : Ω) :
    (∑ i, ‖L.selectedCoefficient a ω i‖ ^ r) =
      ∑ i : L.retained ω, ‖a i / (L.marginal i : ℂ)‖ ^ r := by
  have heq (i : ι) : ‖L.selectedCoefficient a ω i‖ ^ r =
      if i ∈ L.retained ω then ‖a i / (L.marginal i : ℂ)‖ ^ r else 0 := by
    unfold FiniteSelectionLaw.selectedCoefficient
    split_ifs <;> simp [Real.zero_rpow hr.ne']
  simp_rw [heq]
  exact sum_subset_indicator _ _

theorem lpNorm_finiteFourierSum_eq (ν : Measure ℝ) (frequency : ι → ℝ) (a : ι → ℂ)
    {p : ℝ} (hp : 0 < p) :
    lpNorm (finiteFourierSum frequency a) (ENNReal.ofReal p) ν =
      (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top
    (continuous_finiteFourierSum frequency a).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  simp only [one_div]

/-- Averaging inverse-marginal reconstructions costs exactly the expected
`ℓ^r` coefficient mass. All Fourier estimates here are already proved. -/
theorem selected_fourier_gain (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → ℝ) (a : ι → ℂ)
    {gap D p : ℝ} (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hπ : ∀ i, 0 < L.marginal i)
    (hsep : ∀ ω, 0 < L.weight ω → Separated (fun i : L.retained ω => frequency i) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hr : 1 ≤ fourierInterpolationExponent D p) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) ≤
      (∑ i, L.marginal i * (‖a i‖ / L.marginal i) ^ fourierInterpolationExponent D p) ^
        (1 / fourierInterpolationExponent D p) := by
  let r := fourierInterpolationExponent D p
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by dsimp [r]; linarith
  let G : Ω → ℝ → ℂ := fun ω => finiteFourierSum frequency (L.selectedCoefficient a ω)
  have hterm (ω : Ω) : lpNorm (fun t => (L.weight ω : ℂ) * G ω t) (ENNReal.ofReal p) ν ≤
      L.weight ω * (∑ i, ‖L.selectedCoefficient a ω i‖ ^ r) ^ (1 / r) := by
    change lpNorm ((L.weight ω : ℂ) • G ω) (ENNReal.ofReal p) ν ≤ _
    rw [lpNorm_const_smul]
    change ‖(L.weight ω : ℂ)‖ * lpNorm (G ω) (ENNReal.ofReal p) ν ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (L.nonnegative ω)]
    by_cases hw : L.weight ω = 0
    · simp [hw]
    have hwpos : 0 < L.weight ω := lt_of_le_of_ne (L.nonnegative ω) (Ne.symm hw)
    apply mul_le_mul_of_nonneg_left _ (L.nonnegative ω)
    have heq : G ω = finiteFourierSum (fun i : L.retained ω => frequency i)
        (fun i : L.retained ω => a i / (L.marginal i : ℂ)) := by
      funext t
      exact selectedFourier_eq_subtype L frequency a ω t
    rw [heq, lpNorm_finiteFourierSum_eq ν _ _ hp0]
    have hg := finite_fourier_gain ν (fun i : L.retained ω => frequency i)
      (fun i : L.retained ω => a i / (L.marginal i : ℂ))
      hgap (hsep ω hwpos) hν hD (by simpa using hcard ω hwpos) hp
    simpa only [sequenceNorm, selected_power_sum_eq_subtype L a hr0 ω] using hg
  have hmem (ω : Ω) : MemLp (fun t => (L.weight ω : ℂ) * G ω t) (ENNReal.ofReal p) ν := by
    apply (MemLp.of_bound (continuous_finiteFourierSum frequency
      (L.selectedCoefficient a ω)).aestronglyMeasurable
      (∑ i, ‖L.selectedCoefficient a ω i‖)
      (Filter.Eventually.of_forall (finiteFourierSum_bound frequency (L.selectedCoefficient a ω)))).const_mul
  have hexpect : (∑ ω, fun t => (L.weight ω : ℂ) * G ω t) = finiteFourierSum frequency a := by
    funext t
    simpa only [Finset.sum_apply] using
      L.expected_selectedFourier (fun i => (hπ i).ne') frequency a t
  calc
    _ = lpNorm (finiteFourierSum frequency a) (ENNReal.ofReal p) ν :=
      (lpNorm_finiteFourierSum_eq ν frequency a hp0).symm
    _ ≤ ∑ ω, lpNorm (fun t => (L.weight ω : ℂ) * G ω t) (ENNReal.ofReal p) ν := by
      rw [← hexpect]
      exact lpNorm_sum_le (s := Finset.univ) (fun ω _ => hmem ω)
        (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1 ≤ p by linarith))
    _ ≤ ∑ ω, L.weight ω * (∑ i, ‖L.selectedCoefficient a ω i‖ ^ r) ^ (1 / r) :=
      Finset.sum_le_sum (fun ω _ => hterm ω)
    _ ≤ (∑ ω, L.weight ω * ∑ i, ‖L.selectedCoefficient a ω i‖ ^ r) ^ (1 / r) :=
      selection_jensen L _ (fun ω => Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) hr
    _ = _ := by rw [L.selected_cost_expectation a hr0 hπ]

theorem weighted_coefficient_cost (l : ι → ℝ) (X lambda : ι → ℂ) (π q : ι → ℝ)
    {μ r : ℝ} (hl : ∀ i, 0 ≤ l i) (hπ : ∀ i, 0 < π i) (hq : ∀ i, 0 < q i)
    (hqπ : ∀ i, q i ≤ π i) (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ μ)
    (hr : 1 ≤ r) (hμr : μ * r = r - 1) :
    (∑ i, π i * (‖((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i * X i‖ / π i) ^ r) ≤
      ∑ i, l i * ‖X i‖ ^ r := by
  apply Finset.sum_le_sum
  intro i _
  have hpower : ‖((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i * X i‖ ^ r =
      l i * ‖lambda i‖ ^ r * ‖X i‖ ^ r := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hl i) _),
      Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (hl i) _) (norm_nonneg _)) (norm_nonneg _),
      Real.mul_rpow (Real.rpow_nonneg (hl i) _) (norm_nonneg _),
      ← Real.rpow_mul (hl i)]
    have he : (1 - μ) * r = 1 := by nlinarith
    rw [he, Real.rpow_one]
  have hcancel : π i ^ (1 - r) * ‖lambda i‖ ^ r ≤ 1 := by
    refine (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hlambda i) (by linarith))
      (Real.rpow_nonneg (hπ i).le _)).trans ?_
    exact retention_cancellation (hπ i) (hq i) (hqπ i) hr hμr
  calc
    _ = π i ^ (1 - r) * (l i * ‖lambda i‖ ^ r * ‖X i‖ ^ r) := by
      rw [Real.div_rpow (norm_nonneg _) (hπ i).le, hpower,
        Real.rpow_sub (hπ i), Real.rpow_one]
      ring
    _ = (π i ^ (1 - r) * ‖lambda i‖ ^ r) * (l i * ‖X i‖ ^ r) := by ring
    _ ≤ 1 * (l i * ‖X i‖ ^ r) :=
      mul_le_mul_of_nonneg_right hcancel (mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _))
    _ = _ := one_mul _

/-- The scalar inequality `pred:weighted-phase-bound` for a finite
selection law with the stated separation and marginal guarantees. -/
theorem weighted_phase_bound (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → ℝ)
    (l q : ι → ℝ) (X lambda : ι → ℂ) {gap D p μ : ℝ}
    (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hsep : ∀ ω, 0 < L.weight ω → Separated (fun i : L.retained ω => frequency i) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hq : ∀ i, 0 < q i) (hqπ : ∀ i, q i ≤ L.marginal i)
    (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ μ)
    (hr : 1 ≤ fourierInterpolationExponent D p)
    (hrp : fourierInterpolationExponent D p ≤ p)
    (hμr : μ * fourierInterpolationExponent D p = fourierInterpolationExponent D p - 1) :
    (∫ t, ‖finiteFourierSum frequency (fun i => ((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i * X i) t‖ ^ p ∂ν) ^
      (1 / p) ≤ (∑ i, l i * ‖X i‖ ^ p) ^ (1 / p) := by
  have hπ : ∀ i, 0 < L.marginal i := fun i => (hq i).trans_le (hqπ i)
  have hr0 : 0 < fourierInterpolationExponent D p := by linarith
  have hsel := selected_fourier_gain L ν frequency
    (fun i => ((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i * X i) hgap hν hD hp hπ hsep hcard hr
  have hcost := weighted_coefficient_cost l X lambda L.marginal q hl hπ hq hqπ hlambda hr hμr
  refine hsel.trans ((Real.rpow_le_rpow ?_ hcost (show 0 ≤ 1 / fourierInterpolationExponent D p by positivity)).trans ?_)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hπ i).le
      (Real.rpow_nonneg (div_nonneg (norm_nonneg _) (hπ i).le) _)
  · exact weighted_power_mean l (fun i => ‖X i‖) hl (fun i => norm_nonneg _) htotal hr0 hrp

/-- Add the mass baseline and divide by its constant denominator. -/
theorem weighted_prediction_average (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → ℝ)
    (l q : ι → ℝ) (X lambda : ι → ℂ) {gap D p μ : ℝ}
    (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hsep : ∀ ω, 0 < L.weight ω → Separated (fun i : L.retained ω => frequency i) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hq : ∀ i, 0 < q i) (hqπ : ∀ i, q i ≤ L.marginal i)
    (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ μ)
    (hr : 1 ≤ fourierInterpolationExponent D p)
    (hrp : fourierInterpolationExponent D p ≤ p)
    (hμr : μ * fourierInterpolationExponent D p = fourierInterpolationExponent D p - 1) :
    (∫ t, (1 + ‖finiteFourierSum frequency (fun i => ((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i * X i) t‖ ^ p) /
      (1 + ∑ i, l i * ‖X i‖ ^ p) ∂ν) ≤ 1 := by
  have hp0 : 0 < p := by linarith
  let a : ι → ℂ := fun i => ((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i * X i
  have hS : 0 ≤ ∑ i, l i * ‖X i‖ ^ p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _)
  have hroot := weighted_phase_bound L ν frequency l q X lambda hgap hν hD hp hsep hcard
    hl htotal hq hqπ hlambda hr hrp hμr
  have hmoment : (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ≤ ∑ i, l i * ‖X i‖ ^ p :=
    (Real.rpow_le_rpow_iff (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) hS
      (one_div_pos.mpr hp0)).mp hroot
  have hmem : MemLp (finiteFourierSum frequency a) (ENNReal.ofReal p) ν :=
    MemLp.of_bound (continuous_finiteFourierSum frequency a).aestronglyMeasurable
      (∑ i, ‖a i‖) (Filter.Eventually.of_forall (finiteFourierSum_bound frequency a))
  have hi : Integrable (fun t => ‖finiteFourierSum frequency a t‖ ^ p) ν := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hmem.integrable_norm_rpow'
  rw [integral_div, integral_add (integrable_const 1) hi]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact (div_le_one (by linarith : 0 < 1 + ∑ i, l i * ‖X i‖ ^ p)).2 (by linarith)

def phaseMu (D p : ℝ) : ℝ := (1 + phaseParameter D) / p

omit [Fintype Ω] [Fintype ι] in
theorem phase_selection_parameters {D p : ℝ} (hD : 1 ≤ D) (hp : 4 ≤ p) :
    1 ≤ fourierInterpolationExponent D p ∧ fourierInterpolationExponent D p ≤ p ∧
      phaseMu D p * fourierInterpolationExponent D p = fourierInterpolationExponent D p - 1 := by
  have hp0 : 0 < p := by linarith
  have hθ := phaseParameter_range hD
  have hθ0 : 0 < phaseParameter D := hθ.1
  have hθ1 : phaseParameter D ≤ 1 / 3 := hθ.2
  have hμ0 : 0 < phaseMu D p := div_pos (by linarith) hp0
  have hμ1 : phaseMu D p ≤ 1 / 3 := (div_le_iff₀ hp0).2 (by linarith)
  have hd : 0 < 1 - phaseMu D p := by linarith
  have hpr : (1 - phaseMu D p) * fourierInterpolationExponent D p = 1 := by
    change (1 - phaseMu D p) * (1 / (1 - phaseMu D p)) = 1
    exact mul_one_div_cancel hd.ne'
  have hpmu : p * phaseMu D p = 1 + phaseParameter D := by
    unfold phaseMu
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · change 1 ≤ 1 / (1 - phaseMu D p)
    exact (le_div_iff₀ hd).2 (by linarith)
  · change 1 / (1 - phaseMu D p) ≤ p
    exact (div_le_iff₀ hd).2 (by nlinarith)
  · nlinarith

theorem weighted_prediction_average_at_p (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → ℝ)
    (l q : ι → ℝ) (X lambda : ι → ℂ) {gap D p : ℝ}
    (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hsep : ∀ ω, 0 < L.weight ω → Separated (fun i : L.retained ω => frequency i) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hq : ∀ i, 0 < q i) (hqπ : ∀ i, q i ≤ L.marginal i)
    (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ phaseMu D p) :
    (∫ t, (1 + ‖finiteFourierSum frequency
        (fun i => ((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i * X i) t‖ ^ p) /
      (1 + ∑ i, l i * ‖X i‖ ^ p) ∂ν) ≤ 1 := by
  obtain ⟨hr, hrp, hμr⟩ := phase_selection_parameters hD hp
  exact weighted_prediction_average L ν frequency l q X lambda hgap hν hD hp hsep hcard
    hl htotal hq hqπ hlambda hr hrp hμr

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
