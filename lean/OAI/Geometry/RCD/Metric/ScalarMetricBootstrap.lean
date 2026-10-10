import OAI.Geometry.RCD.Sobolev.ScalarAbsorption
import OAI.Geometry.RCD.Metric.VolumeBudget

namespace OAI

/-!
# Finite-scale scalar metric bootstrap

Fixing a testing point and a direction turns the manuscript's matrix estimates
into real sequences.  Here `z` is the local mass in that direction, `d` is the
weighted defect, and `b` is the normalized diagonal second derivative.  The
signed first-order errors and nonnegative squared increment are kept explicit.

Finite summation and Cauchy--Schwarz estimates close the bootstrap from
these scalar premises, without further geometric assumptions.
-/

open scoped BigOperators
open Filter
open scoped Topology

namespace RegularPointCoordinates

/-- Monotonicity of the scale metrics converts the unweighted defect budget
to the weighted one used in the metric estimate. -/
theorem weighted_defect_sum_le {e H : ℕ → ℝ} {epsilon Q : ℝ}
    (he : ∀ i, 0 ≤ e i) (hQ : 0 ≤ Q) (k : ℕ)
    (hH : ∀ i < k, H i ≤ Q)
    (hebudget : (∑ i ∈ Finset.range k, e i) ≤ epsilon) :
    (∑ i ∈ Finset.range k, e i * H i) ≤ epsilon * Q := by
  calc
    _ ≤ ∑ i ∈ Finset.range k, e i * Q := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hH i (Finset.mem_range.mp hi)) (he i)
    _ = (∑ i ∈ Finset.range k, e i) * Q := by rw [Finset.sum_mul]
    _ ≤ epsilon * Q := mul_le_mul_of_nonneg_right hebudget hQ

/-- The cumulative upper/lower local-mass comparisons imply the leading
metric comparison before the signed error is introduced. -/
theorem leading_metric_comparison {s z : ℕ → ℝ} {base Q T : ℝ}
    (hbase : 0 ≤ base) (hT : 0 < T) (hs : ∀ i, 0 ≤ s i) (k : ℕ)
    (hsz : ∀ i < k, s i ≤ z i)
    (hlower : Q ≤ T * (base + ∑ i ∈ Finset.range k, s i))
    (hupper : base + (∑ i ∈ Finset.range k, z i) ≤ T * Q) :
    T⁻¹ * Q ≤ base + 2 * (∑ i ∈ Finset.range k, s i) ∧
      base + 2 * (∑ i ∈ Finset.range k, s i) ≤ 2 * T * Q := by
  have hsum := Finset.sum_le_sum (fun i hi => hsz i (Finset.mem_range.mp hi))
  have hsumPos : 0 ≤ ∑ i ∈ Finset.range k, s i :=
    Finset.sum_nonneg fun i _ => hs i
  have hdiv : Q / T ≤ base + ∑ i ∈ Finset.range k, s i :=
    (div_le_iff₀ hT).mpr (by nlinarith [hlower])
  rw [div_eq_inv_mul] at hdiv
  constructor <;> nlinarith

/-- Cauchy--Schwarz for square roots of nonnegative scalar budgets. -/
theorem sum_sqrt_mul_sqrt_le {z d : ℕ → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hd : ∀ i, 0 ≤ d i) (k : ℕ) :
    (∑ i ∈ Finset.range k, Real.sqrt (z i) * Real.sqrt (d i)) ≤
      Real.sqrt (∑ i ∈ Finset.range k, z i) *
        Real.sqrt (∑ i ∈ Finset.range k, d i) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range k)
    (fun i => Real.sqrt (z i)) (fun i => Real.sqrt (d i))
  have hzsq : (∑ i ∈ Finset.range k, (Real.sqrt (z i)) ^ 2) =
      ∑ i ∈ Finset.range k, z i :=
    Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hz i)
  have hdsq : (∑ i ∈ Finset.range k, (Real.sqrt (d i)) ^ 2) =
      ∑ i ∈ Finset.range k, d i :=
    Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hd i)
  rwa [hzsq, hdsq] at hcs

/-- The diagonal recurrence converts the forcing budgets to a square sum. -/
theorem diagonal_recurrence_square_budget {z d b : ℕ → ℝ} {C : ℝ}
    (hz : ∀ i, 0 ≤ z i) (hd : ∀ i, 0 ≤ d i) (hb : ∀ i, 0 ≤ b i)
    (hbzero : b 0 = 0) (k : ℕ)
    (hrec : ∀ i < k, b (i + 1) ≤ b i / 2 +
      C * (Real.sqrt (z i) + Real.sqrt (d i))) :
    (∑ i ∈ Finset.range k, b i ^ 2) ≤
      8 * C ^ 2 * ((∑ i ∈ Finset.range k, z i) +
        ∑ i ∈ Finset.range k, d i) := by
  have hrecSum := contracting_recurrence_sq_sum_upto k hbzero hb hrec
  have hforcing : (∑ i ∈ Finset.range k,
      (Real.sqrt (z i) + Real.sqrt (d i)) ^ 2) ≤
      2 * ((∑ i ∈ Finset.range k, z i) + ∑ i ∈ Finset.range k, d i) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, 2 * (z i + d i) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [Real.sq_sqrt (hz i), Real.sq_sqrt (hd i),
          sq_nonneg (Real.sqrt (z i) - Real.sqrt (d i))]
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hscaled := mul_le_mul_of_nonneg_left hforcing
    (by positivity : 0 ≤ 4 * C ^ 2)
  nlinarith [sq_nonneg (b k)]

/-- Summing the exact metric increment and estimating its three errors.
Only the displayed finite-scale premises are used. -/
theorem scalar_metric_cumulative_error {m s z d b linear inverse square : ℕ → ℝ}
    {C epsilon : ℝ} (hC : 0 ≤ C)
    (hz : ∀ i, 0 ≤ z i) (hd : ∀ i, 0 ≤ d i) (hb : ∀ i, 0 ≤ b i)
    (hbzero : b 0 = 0) (k : ℕ)
    (hrec : ∀ i < k, b (i + 1) ≤ b i / 2 +
      C * (Real.sqrt (z i) + Real.sqrt (d i)))
    (hlinear : ∀ i < k, |linear i| ≤ C * Real.sqrt (z i) * Real.sqrt (d i))
    (hinverse : ∀ i < k, |inverse i| ≤ C * b i * Real.sqrt (d i))
    (hsquare : ∀ i < k, |square i| ≤ C * epsilon * (z i + d i))
    (hstep : ∀ i < k, m (i + 1) - m i =
      2 * s i + 2 * linear i + 2 * inverse i + square i) :
    |m k - m 0 - 2 * ∑ i ∈ Finset.range k, s i| ≤
      2 * C * Real.sqrt (∑ i ∈ Finset.range k, z i) *
          Real.sqrt (∑ i ∈ Finset.range k, d i) +
      2 * C * Real.sqrt (8 * C ^ 2 *
          ((∑ i ∈ Finset.range k, z i) + ∑ i ∈ Finset.range k, d i)) *
          Real.sqrt (∑ i ∈ Finset.range k, d i) +
      C * epsilon * ((∑ i ∈ Finset.range k, z i) +
        ∑ i ∈ Finset.range k, d i) := by
  have htel : m k - m 0 - 2 * ∑ i ∈ Finset.range k, s i =
      ∑ i ∈ Finset.range k, (2 * linear i + 2 * inverse i + square i) := by
    rw [← volume_profile_increment_sum m k, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hstep i (Finset.mem_range.mp hi)]
    ring
  rw [htel]
  have habs : |∑ i ∈ Finset.range k, (2 * linear i + 2 * inverse i + square i)| ≤
      2 * C * (∑ i ∈ Finset.range k, Real.sqrt (z i) * Real.sqrt (d i)) +
      2 * C * (∑ i ∈ Finset.range k, b i * Real.sqrt (d i)) +
      C * epsilon * ((∑ i ∈ Finset.range k, z i) +
        ∑ i ∈ Finset.range k, d i) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, |2 * linear i + 2 * inverse i + square i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range k,
          (2 * C * (Real.sqrt (z i) * Real.sqrt (d i)) +
          2 * C * (b i * Real.sqrt (d i)) + C * epsilon * (z i + d i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have htriangle := (abs_add_le (2 * linear i + 2 * inverse i) (square i)).trans
          (add_le_add (abs_add_le (2 * linear i) (2 * inverse i)) le_rfl)
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htriangle
        nlinarith [hlinear i (Finset.mem_range.mp hi),
          hinverse i (Finset.mem_range.mp hi), hsquare i (Finset.mem_range.mp hi)]
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcsInverse := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range k)
    b (fun i => Real.sqrt (d i))
  have hdsq : (∑ i ∈ Finset.range k, (Real.sqrt (d i)) ^ 2) =
      ∑ i ∈ Finset.range k, d i :=
    Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hd i)
  rw [hdsq] at hcsInverse
  have hdiag := diagonal_recurrence_square_budget hz hd hb hbzero k hrec
  have hcsInverse' : (∑ i ∈ Finset.range k, b i * Real.sqrt (d i)) ≤
      Real.sqrt (8 * C ^ 2 * ((∑ i ∈ Finset.range k, z i) +
        ∑ i ∈ Finset.range k, d i)) * Real.sqrt (∑ i ∈ Finset.range k, d i) :=
    hcsInverse.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hdiag)
      (Real.sqrt_nonneg _))
  have hlinearSum := mul_le_mul_of_nonneg_left (sum_sqrt_mul_sqrt_le hz hd k)
    (by positivity : 0 ≤ 2 * C)
  have hinverseSum := mul_le_mul_of_nonneg_left hcsInverse'
    (by positivity : 0 ≤ 2 * C)
  nlinarith

/-- An explicit coefficient for the cumulative metric error after using
the local-mass and weighted-defect budgets. -/
noncomputable def scalarMetricErrorCoefficient (C T epsilon : ℝ) : ℝ :=
  2 * C * Real.sqrt T * Real.sqrt epsilon +
    2 * C * Real.sqrt (8 * C ^ 2 * (T + epsilon)) * Real.sqrt epsilon +
    C * epsilon * (T + epsilon)

/-- The coefficient can be made arbitrarily small after fixing `C` and `T`. -/
theorem scalarMetricErrorCoefficient_tendsto_zero (C T : ℝ) :
    Tendsto (scalarMetricErrorCoefficient C T) (𝓝 0) (𝓝 0) := by
  have hcont : Continuous (scalarMetricErrorCoefficient C T) := by
    unfold scalarMetricErrorCoefficient
    fun_prop
  simpa [scalarMetricErrorCoefficient] using hcont.tendsto 0

/-- The full finite metric error is proportional to the final directional
metric `Q`, even if that metric grows with the scale. -/
theorem scalar_metric_error_of_budgets {m s z d b linear inverse square : ℕ → ℝ}
    {C T epsilon Q : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hepsilon : 0 ≤ epsilon) (hQ : 0 ≤ Q)
    (hz : ∀ i, 0 ≤ z i) (hd : ∀ i, 0 ≤ d i) (hb : ∀ i, 0 ≤ b i)
    (hbzero : b 0 = 0) (k : ℕ)
    (hrec : ∀ i < k, b (i + 1) ≤ b i / 2 +
      C * (Real.sqrt (z i) + Real.sqrt (d i)))
    (hlinear : ∀ i < k, |linear i| ≤ C * Real.sqrt (z i) * Real.sqrt (d i))
    (hinverse : ∀ i < k, |inverse i| ≤ C * b i * Real.sqrt (d i))
    (hsquare : ∀ i < k, |square i| ≤ C * epsilon * (z i + d i))
    (hstep : ∀ i < k, m (i + 1) - m i =
      2 * s i + 2 * linear i + 2 * inverse i + square i)
    (hzbudget : (∑ i ∈ Finset.range k, z i) ≤ T * Q)
    (hdbudget : (∑ i ∈ Finset.range k, d i) ≤ epsilon * Q) :
    |m k - m 0 - 2 * ∑ i ∈ Finset.range k, s i| ≤
      scalarMetricErrorCoefficient C T epsilon * Q := by
  have hraw := scalar_metric_cumulative_error hC hz hd hb hbzero k
    hrec hlinear hinverse hsquare hstep
  have hsum : ((∑ i ∈ Finset.range k, z i) +
      ∑ i ∈ Finset.range k, d i) ≤ (T + epsilon) * Q := by
    nlinarith
  have hfirst : 2 * C * Real.sqrt (∑ i ∈ Finset.range k, z i) *
      Real.sqrt (∑ i ∈ Finset.range k, d i) ≤
      2 * C * Real.sqrt (T * Q) * Real.sqrt (epsilon * Q) := by
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hzbudget) (by positivity))
      (Real.sqrt_le_sqrt hdbudget) (Real.sqrt_nonneg _) (by positivity)
  have hsecond : 2 * C * Real.sqrt (8 * C ^ 2 *
      ((∑ i ∈ Finset.range k, z i) + ∑ i ∈ Finset.range k, d i)) *
      Real.sqrt (∑ i ∈ Finset.range k, d i) ≤
      2 * C * Real.sqrt ((8 * C ^ 2 * (T + epsilon)) * Q) *
      Real.sqrt (epsilon * Q) := by
    apply mul_le_mul _ (Real.sqrt_le_sqrt hdbudget) (Real.sqrt_nonneg _) (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 8 * C ^ 2)]
  have hthird := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg hC hepsilon)
  refine hraw.trans ((add_le_add (add_le_add hfirst hsecond) hthird).trans_eq ?_)
  rw [Real.sqrt_mul hT Q, Real.sqrt_mul hepsilon Q,
    Real.sqrt_mul (by positivity : 0 ≤ 8 * C ^ 2 * (T + epsilon)) Q]
  calc
    _ = scalarMetricErrorCoefficient C T epsilon * (Real.sqrt Q) ^ 2 := by
      unfold scalarMetricErrorCoefficient
      ring_nf
      rw [Real.sq_sqrt hQ]
      ring
    _ = _ := by rw [Real.sq_sqrt hQ]

/-- Leading metric comparison and a small cumulative error close the bootstrap. -/
theorem scalar_metric_comparison_closes {M leading Q T eta : ℝ}
    (hQ : 0 ≤ Q) (hT : 0 < T)
    (hlower : T⁻¹ * Q ≤ leading) (hupper : leading ≤ 2 * T * Q)
    (herror : |M - leading| ≤ eta * Q) (hsmall : eta ≤ (2 * T)⁻¹) :
    (2 * T)⁻¹ * Q ≤ M ∧ M ≤ (2 * T + (2 * T)⁻¹) * Q := by
  have heta := mul_le_mul_of_nonneg_right hsmall hQ
  have hinv : T⁻¹ = 2 * (2 * T)⁻¹ := by
    field_simp [ne_of_gt hT]
  have hlower' : 2 * ((2 * T)⁻¹ * Q) ≤ leading := by
    calc
      _ = T⁻¹ * Q := by rw [hinv]; ring
      _ ≤ leading := hlower
  have habs := abs_le.mp herror
  constructor <;> nlinarith

/-- Choosing the bootstrap constant `4T` gives its lower and upper bounds. -/
theorem scalar_metric_fourfold_comparison {M leading Q T eta : ℝ}
    (hQ : 0 ≤ Q) (hT : 1 ≤ T)
    (hlower : T⁻¹ * Q ≤ leading) (hupper : leading ≤ 2 * T * Q)
    (herror : |M - leading| ≤ eta * Q) (hsmall : eta ≤ (2 * T)⁻¹) :
    (4 * T)⁻¹ * Q ≤ M ∧ M ≤ (4 * T) * Q := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  obtain ⟨hl, hu⟩ := scalar_metric_comparison_closes hQ hTpos
    hlower hupper herror hsmall
  have hinv : (4 * T)⁻¹ ≤ (2 * T)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have hcoeff : 2 * T + (2 * T)⁻¹ ≤ 4 * T := by
    have := inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ 2 * T)
    linarith
  exact ⟨(mul_le_mul_of_nonneg_right hinv hQ).trans hl,
    hu.trans (mul_le_mul_of_nonneg_right hcoeff hQ)⟩

/-- The scalar recurrence, three error estimates, two budgets, and leading
comparison imply the metric bootstrap bounds. -/
theorem scalar_metric_bootstrap {m s z d b linear inverse square : ℕ → ℝ}
    {C T epsilon Q : ℝ} (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hepsilon : 0 ≤ epsilon) (hQ : 0 ≤ Q)
    (hz : ∀ i, 0 ≤ z i) (hd : ∀ i, 0 ≤ d i) (hb : ∀ i, 0 ≤ b i)
    (hbzero : b 0 = 0) (k : ℕ)
    (hrec : ∀ i < k, b (i + 1) ≤ b i / 2 +
      C * (Real.sqrt (z i) + Real.sqrt (d i)))
    (hlinear : ∀ i < k, |linear i| ≤ C * Real.sqrt (z i) * Real.sqrt (d i))
    (hinverse : ∀ i < k, |inverse i| ≤ C * b i * Real.sqrt (d i))
    (hsquare : ∀ i < k, |square i| ≤ C * epsilon * (z i + d i))
    (hstep : ∀ i < k, m (i + 1) - m i =
      2 * s i + 2 * linear i + 2 * inverse i + square i)
    (hzbudget : (∑ i ∈ Finset.range k, z i) ≤ T * Q)
    (hdbudget : (∑ i ∈ Finset.range k, d i) ≤ epsilon * Q)
    (hleadLower : T⁻¹ * Q ≤ m 0 + 2 * ∑ i ∈ Finset.range k, s i)
    (hleadUpper : m 0 + 2 * ∑ i ∈ Finset.range k, s i ≤ 2 * T * Q)
    (hsmall : scalarMetricErrorCoefficient C T epsilon ≤ (2 * T)⁻¹) :
    (4 * T)⁻¹ * Q ≤ m k ∧ m k ≤ (4 * T) * Q := by
  have herr := scalar_metric_error_of_budgets hC (zero_le_one.trans hT)
    hepsilon hQ hz hd hb hbzero k hrec hlinear hinverse hsquare hstep hzbudget hdbudget
  have herr' : |m k - (m 0 + 2 * ∑ i ∈ Finset.range k, s i)| ≤
      scalarMetricErrorCoefficient C T epsilon * Q := by
    simpa only [sub_add_eq_sub_sub] using herr
  exact scalar_metric_fourfold_comparison hQ hT hleadLower hleadUpper herr' hsmall

end RegularPointCoordinates

end OAI
