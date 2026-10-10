import OAI.Analysis.LipschitzHilbert.Phase.PhaseSelection
import OAI.Analysis.LipschitzHilbert.Fourier.HilbertFourierGain
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-!
# Averaging diagonal Hilbert-valued phases

The weighted prediction bound of §9 for finite-dimensional Hilbert vectors and
coordinate-dependent frequencies. The retained-set estimate is the proved
constant-one diagonal Fourier gain; the marginal cancellation is exact.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

omit [Fintype Ω] [Fintype ι] [Fintype κ] in
theorem euclidean_sum_apply {α : Type*} (s : Finset α)
    (f : α → EuclideanSpace ℂ κ) (j : κ) :
    (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

omit [Fintype Ω] [Fintype ι] in
theorem euclidean_norm_rpow (v : EuclideanSpace ℂ κ) (p : ℝ) :
    ‖v‖ ^ p = (∑ j, ‖v j‖ ^ 2) ^ (p / 2) := by
  rw [← EuclideanSpace.norm_sq_eq, ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- Coordinatewise modulation by unit characters. -/
def diagonalModulation (frequency : κ → ℝ) (a : EuclideanSpace ℂ κ) (t : ℝ) :
    EuclideanSpace ℂ κ := WithLp.toLp 2 (fun j => a j * character (frequency j) t)

omit [Fintype Ω] [Fintype ι] in
theorem norm_diagonalModulation (frequency : κ → ℝ) (a : EuclideanSpace ℂ κ) (t : ℝ) :
    ‖diagonalModulation frequency a t‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, diagonalModulation,
    norm_mul, norm_character, mul_one]

/-- A diagonal phase sum, represented in the actual Euclidean Hilbert norm. -/
def diagonalFourierSum (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ)
    (t : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun j => finiteFourierSum (fun i => frequency i j) (fun i => a i j) t)

omit [Fintype Ω] [Fintype κ] in
theorem diagonalFourierSum_eq_sum (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (t : ℝ) :
    diagonalFourierSum frequency a t = ∑ i, diagonalModulation (frequency i) (a i) t := by
  apply PiLp.ext
  intro j
  rw [euclidean_sum_apply]
  rfl

omit [Fintype Ω] [Fintype κ] in
theorem continuous_diagonalFourierSum (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) : Continuous (diagonalFourierSum frequency a) :=
  (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
    (continuous_pi (fun _ => continuous_finiteFourierSum _ _))

omit [Fintype Ω] in
theorem diagonalFourierSum_bound (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (t : ℝ) :
    ‖diagonalFourierSum frequency a t‖ ≤ ∑ i, ‖a i‖ := by
  rw [diagonalFourierSum_eq_sum]
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl (fun i _ =>
    norm_diagonalModulation (frequency i) (a i) t))

omit [Fintype Ω] in
theorem lpNorm_diagonalFourierSum_eq (ν : Measure ℝ) (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) {p : ℝ} (hp : 0 < p) :
    lpNorm (diagonalFourierSum frequency a) (ENNReal.ofReal p) ν =
      (∫ t, ‖diagonalFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top
    (continuous_diagonalFourierSum frequency a).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  simp only [one_div]

omit [Fintype Ω] in
theorem diagonal_fourier_gain_norm (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : ∀ j, Separated (fun i => frequency i j) gap)
    (hν : FourierGap ν gap) (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hp : 4 ≤ p) :
    (∫ t, ‖diagonalFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) ≤
      (∑ i, ‖a i‖ ^ fourierInterpolationExponent D p) ^
        (1 / fourierInterpolationExponent D p) := by
  simpa only [euclidean_norm_rpow, diagonalFourierSum, PiLp.toLp_apply] using
    diagonal_finite_fourier_gain ν frequency (fun i j => a i j) hgap hsep hν hD hcard hp

namespace FiniteSelectionLaw

def selectedVector (L : FiniteSelectionLaw Ω ι) (a : ι → EuclideanSpace ℂ κ)
    (ω : Ω) (i : ι) : EuclideanSpace ℂ κ :=
  if i ∈ L.retained ω then (L.marginal i : ℂ)⁻¹ • a i else 0

omit [Fintype ι] [Fintype κ] in
theorem selectedVector_apply (L : FiniteSelectionLaw Ω ι) (a : ι → EuclideanSpace ℂ κ)
    (ω : Ω) (i : ι) (j : κ) :
    L.selectedVector a ω i j = L.selectedCoefficient (fun i => a i j) ω i := by
  unfold selectedVector selectedCoefficient
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

omit [Fintype ι] in
theorem norm_selectedVector (L : FiniteSelectionLaw Ω ι) (a : ι → EuclideanSpace ℂ κ)
    (ω : Ω) (i : ι) (hπ : 0 < L.marginal i) :
    ‖L.selectedVector a ω i‖ =
      if i ∈ L.retained ω then ‖a i‖ / L.marginal i else 0 := by
  unfold selectedVector
  split_ifs <;> simp [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hπ, div_eq_mul_inv, mul_comm]

omit [Fintype κ] in
theorem expected_selectedDiagonal (L : FiniteSelectionLaw Ω ι)
    (hπ : ∀ i, L.marginal i ≠ 0) (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (t : ℝ) :
    (∑ ω, (L.weight ω : ℂ) • diagonalFourierSum frequency (L.selectedVector a ω) t) =
      diagonalFourierSum frequency a t := by
  apply PiLp.ext
  intro j
  rw [euclidean_sum_apply]
  simpa only [PiLp.smul_apply, smul_eq_mul, diagonalFourierSum, PiLp.toLp_apply,
    selectedVector_apply] using
    L.expected_selectedFourier hπ (fun i => frequency i j) (fun i => a i j) t

theorem selected_vector_cost (L : FiniteSelectionLaw Ω ι) (a : ι → EuclideanSpace ℂ κ)
    {r : ℝ} (hr : 0 < r) (hπ : ∀ i, 0 < L.marginal i) :
    (∑ ω, L.weight ω * ∑ i, ‖L.selectedVector a ω i‖ ^ r) =
      ∑ i, L.marginal i * (‖a i‖ / L.marginal i) ^ r := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [marginal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [norm_selectedVector L a ω i (hπ i)]
  split_ifs <;> simp [Real.zero_rpow hr.ne', marginal]

end FiniteSelectionLaw

omit [Fintype κ] in
theorem selectedDiagonal_eq_subtype (L : FiniteSelectionLaw Ω ι)
    (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ) (ω : Ω) (t : ℝ) :
    diagonalFourierSum frequency (L.selectedVector a ω) t =
      diagonalFourierSum (fun i : L.retained ω => frequency i)
        (fun i : L.retained ω => (L.marginal i : ℂ)⁻¹ • a i) t := by
  apply PiLp.ext
  intro j
  simpa only [diagonalFourierSum, PiLp.toLp_apply, FiniteSelectionLaw.selectedVector_apply,
    PiLp.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    selectedFourier_eq_subtype L (fun i => frequency i j) (fun i => a i j) ω t

theorem selected_vector_power_sum_eq_subtype (L : FiniteSelectionLaw Ω ι)
    (a : ι → EuclideanSpace ℂ κ) {r : ℝ} (hr : 0 < r) (ω : Ω) :
    (∑ i, ‖L.selectedVector a ω i‖ ^ r) =
      ∑ i : L.retained ω, ‖(L.marginal i : ℂ)⁻¹ • a i‖ ^ r := by
  have heq (i : ι) : ‖L.selectedVector a ω i‖ ^ r =
      if i ∈ L.retained ω then ‖(L.marginal i : ℂ)⁻¹ • a i‖ ^ r else 0 := by
    unfold FiniteSelectionLaw.selectedVector
    split_ifs <;> simp [Real.zero_rpow hr.ne']
  simp_rw [heq]
  exact sum_subset_indicator _ _

/-- Inverse-marginal averaging of diagonal Hilbert phases. -/
theorem selected_diagonal_fourier_gain (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) {gap D p : ℝ}
    (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hπ : ∀ i, 0 < L.marginal i)
    (hsep : ∀ ω, 0 < L.weight ω → ∀ j,
      Separated (fun i : L.retained ω => frequency i j) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hr : 1 ≤ fourierInterpolationExponent D p) :
    (∫ t, ‖diagonalFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) ≤
      (∑ i, L.marginal i * (‖a i‖ / L.marginal i) ^ fourierInterpolationExponent D p) ^
        (1 / fourierInterpolationExponent D p) := by
  let r := fourierInterpolationExponent D p
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by dsimp [r]; linarith
  let G : Ω → ℝ → EuclideanSpace ℂ κ :=
    fun ω => diagonalFourierSum frequency (L.selectedVector a ω)
  have hterm (ω : Ω) : lpNorm ((L.weight ω : ℂ) • G ω) (ENNReal.ofReal p) ν ≤
      L.weight ω * (∑ i, ‖L.selectedVector a ω i‖ ^ r) ^ (1 / r) := by
    rw [lpNorm_const_smul]
    change ‖(L.weight ω : ℂ)‖ * lpNorm (G ω) (ENNReal.ofReal p) ν ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (L.nonnegative ω)]
    by_cases hw : L.weight ω = 0
    · simp [hw]
    have hwpos : 0 < L.weight ω := lt_of_le_of_ne (L.nonnegative ω) (Ne.symm hw)
    apply mul_le_mul_of_nonneg_left _ (L.nonnegative ω)
    have heq : G ω = diagonalFourierSum (fun i : L.retained ω => frequency i)
        (fun i : L.retained ω => (L.marginal i : ℂ)⁻¹ • a i) := by
      funext t
      exact selectedDiagonal_eq_subtype L frequency a ω t
    rw [heq, lpNorm_diagonalFourierSum_eq ν _ _ hp0]
    have hg := diagonal_fourier_gain_norm ν (fun i : L.retained ω => frequency i)
      (fun i : L.retained ω => (L.marginal i : ℂ)⁻¹ • a i)
      hgap (hsep ω hwpos) hν hD (by simpa using hcard ω hwpos) hp
    simpa only [selected_vector_power_sum_eq_subtype L a hr0 ω] using hg
  have hmem (ω : Ω) : MemLp ((L.weight ω : ℂ) • G ω) (ENNReal.ofReal p) ν := by
    exact (MemLp.of_bound (continuous_diagonalFourierSum frequency
      (L.selectedVector a ω)).aestronglyMeasurable
      (∑ i, ‖L.selectedVector a ω i‖)
      (Filter.Eventually.of_forall (diagonalFourierSum_bound frequency
        (L.selectedVector a ω)))).const_smul _
  have hexpect : (∑ ω, (L.weight ω : ℂ) • G ω) = diagonalFourierSum frequency a := by
    funext t
    simpa only [Finset.sum_apply, Pi.smul_apply] using
      L.expected_selectedDiagonal (fun i => (hπ i).ne') frequency a t
  calc
    _ = lpNorm (diagonalFourierSum frequency a) (ENNReal.ofReal p) ν :=
      (lpNorm_diagonalFourierSum_eq ν frequency a hp0).symm
    _ ≤ ∑ ω, lpNorm ((L.weight ω : ℂ) • G ω) (ENNReal.ofReal p) ν := by
      rw [← hexpect]
      exact lpNorm_sum_le (s := Finset.univ) (fun ω _ => hmem ω)
        (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1 ≤ p by linarith))
    _ ≤ ∑ ω, L.weight ω * (∑ i, ‖L.selectedVector a ω i‖ ^ r) ^ (1 / r) :=
      Finset.sum_le_sum (fun ω _ => hterm ω)
    _ ≤ (∑ ω, L.weight ω * ∑ i, ‖L.selectedVector a ω i‖ ^ r) ^ (1 / r) :=
      selection_jensen L _ (fun ω => Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) hr
    _ = _ := by rw [L.selected_vector_cost a hr0 hπ]

/-- The scalar marginal cancellation applies to Hilbert vectors through their norms. -/
theorem weighted_vector_coefficient_cost (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (π q : ι → ℝ) {μ r : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hπ : ∀ i, 0 < π i) (hq : ∀ i, 0 < q i)
    (hqπ : ∀ i, q i ≤ π i) (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ μ)
    (hr : 1 ≤ r) (hμr : μ * r = r - 1) :
    (∑ i, π i * (‖(((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i) • X i‖ / π i) ^ r) ≤
      ∑ i, l i * ‖X i‖ ^ r := by
  simpa only [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using
    weighted_coefficient_cost l (fun i => (‖X i‖ : ℂ)) lambda π q hl hπ hq hqπ hlambda hr hμr

theorem weighted_diagonal_phase_bound (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → κ → ℝ)
    (l q : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ)
    {gap D p μ : ℝ} (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hsep : ∀ ω, 0 < L.weight ω → ∀ j,
      Separated (fun i : L.retained ω => frequency i j) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hq : ∀ i, 0 < q i) (hqπ : ∀ i, q i ≤ L.marginal i)
    (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ μ)
    (hr : 1 ≤ fourierInterpolationExponent D p)
    (hrp : fourierInterpolationExponent D p ≤ p)
    (hμr : μ * fourierInterpolationExponent D p = fourierInterpolationExponent D p - 1) :
    (∫ t, ‖diagonalFourierSum frequency
      (fun i => (((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i) • X i) t‖ ^ p ∂ν) ^ (1 / p) ≤
      (∑ i, l i * ‖X i‖ ^ p) ^ (1 / p) := by
  have hπ : ∀ i, 0 < L.marginal i := fun i => (hq i).trans_le (hqπ i)
  have hr0 : 0 < fourierInterpolationExponent D p := by linarith
  have hsel := selected_diagonal_fourier_gain L ν frequency
    (fun i => (((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i) • X i) hgap hν hD hp hπ hsep hcard hr
  have hcost := weighted_vector_coefficient_cost l X lambda L.marginal q hl hπ hq hqπ hlambda hr hμr
  refine hsel.trans ((Real.rpow_le_rpow ?_ hcost (show 0 ≤ 1 / fourierInterpolationExponent D p by positivity)).trans ?_)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hπ i).le
      (Real.rpow_nonneg (div_nonneg (norm_nonneg _) (hπ i).le) _)
  · exact weighted_power_mean l (fun i => ‖X i‖) hl (fun i => norm_nonneg _) htotal hr0 hrp

/-- The full finite-dimensional diagonal weighted prediction average of §9. -/
theorem weighted_diagonal_prediction_average_at_p (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → κ → ℝ)
    (l q : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ)
    {gap D p : ℝ} (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hsep : ∀ ω, 0 < L.weight ω → ∀ j,
      Separated (fun i : L.retained ω => frequency i j) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hq : ∀ i, 0 < q i) (hqπ : ∀ i, q i ≤ L.marginal i)
    (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ phaseMu D p) :
    (∫ t, (1 + ‖diagonalFourierSum frequency
      (fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i) t‖ ^ p) /
      (1 + ∑ i, l i * ‖X i‖ ^ p) ∂ν) ≤ 1 := by
  obtain ⟨hr, hrp, hμr⟩ := phase_selection_parameters hD hp
  have hp0 : 0 < p := by linarith
  let a : ι → EuclideanSpace ℂ κ :=
    fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i
  have hS : 0 ≤ ∑ i, l i * ‖X i‖ ^ p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _)
  have hroot := weighted_diagonal_phase_bound L ν frequency l q X lambda hgap hν hD hp
    hsep hcard hl htotal hq hqπ hlambda hr hrp hμr
  have hmoment : (∫ t, ‖diagonalFourierSum frequency a t‖ ^ p ∂ν) ≤ ∑ i, l i * ‖X i‖ ^ p :=
    (Real.rpow_le_rpow_iff (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) hS
      (one_div_pos.mpr hp0)).mp hroot
  have hmem : MemLp (diagonalFourierSum frequency a) (ENNReal.ofReal p) ν :=
    MemLp.of_bound (continuous_diagonalFourierSum frequency a).aestronglyMeasurable
      (∑ i, ‖a i‖) (Filter.Eventually.of_forall (diagonalFourierSum_bound frequency a))
  have hi : Integrable (fun t => ‖diagonalFourierSum frequency a t‖ ^ p) ν := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hmem.integrable_norm_rpow'
  rw [integral_div, integral_add (integrable_const 1) hi]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact (div_le_one (by linarith : 0 < 1 + ∑ i, l i * ‖X i‖ ^ p)).2 (by linarith)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
