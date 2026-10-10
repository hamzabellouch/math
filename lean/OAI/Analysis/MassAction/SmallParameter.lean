import Mathlib

namespace OAI

universe uIota uEta uE

noncomputable section
open Filter Topology
open scoped BigOperators

namespace Problem326

/-- The final small parameter is chosen only after the positive gap is fixed.
The rate type may be empty; the rate inequalities are then vacuous. -/
theorem exists_small_parameter {ι : Type uIota} {η : Type uEta} [Fintype ι] [Fintype η]
    (c : ι → ℝ) (κ : η → ℝ) {H h₀ : ℝ}
    (hH : 0 < H) (hh₀ : 0 < h₀) (hκ : ∀ e, 0 < κ e) :
    ∃ h : ℝ, 0 < h ∧ h < h₀ ∧ h < 1 ∧
      (∀ i, |c i / Real.log h| < H) ∧
      ∀ e, h ^ H * (∑ e, κ e) < κ e := by
  have hpositive : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < h₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hh₀)
  have hone : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  have hlogs : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ i, |c i / Real.log h| < H := by
    apply Filter.eventually_all.2
    intro i
    have ht : Tendsto (fun h : ℝ => |c i / Real.log h|) (𝓝[>] 0) (𝓝 0) := by
      simpa using (Real.tendsto_log_nhdsGT_zero.const_div_atBot (c i)).abs
    exact ht.eventually_lt_const hH
  have hrates : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ e, h ^ H * (∑ e, κ e) < κ e := by
    apply Filter.eventually_all.2
    intro e
    have hpow : Tendsto (fun h : ℝ => h ^ H) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.rpow_const_nhds_zero hH
    have ht : Tendsto (fun h : ℝ => h ^ H * (∑ e, κ e)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hpow.mul_const (∑ e, κ e)
    exact ht.eventually_lt_const (hκ e)
  exact (hpositive.and (hsmall.and (hone.and (hlogs.and hrates)))).exists

/-- Logarithmic coordinates reconstruct a positive state for a base in `(0,1)`. -/
theorem rpow_log_ratio {h x : ℝ} (hh : 0 < h) (hh1 : h < 1) (hx : 0 < x) :
    h ^ (Real.log x / Real.log h) = x := by
  rw [Real.rpow_def_of_pos hh]
  have hlog : Real.log h ≠ 0 := ne_of_lt (Real.log_neg hh hh1)
  rw [mul_div_cancel₀ _ hlog, Real.exp_log hx]

/-- Simultaneous initial-exponent and rate separation with explicit reconstruction. -/
theorem exists_initial_exponent_parameter {ι : Type uIota} {η : Type uEta} [Fintype ι] [Fintype η]
    (x₀ : ι → ℝ) (κ : η → ℝ) {H h₀ : ℝ}
    (hx₀ : ∀ i, 0 < x₀ i) (hH : 0 < H) (hh₀ : 0 < h₀) (hκ : ∀ e, 0 < κ e) :
    ∃ (h : ℝ) (p : ι → ℝ), 0 < h ∧ h < h₀ ∧ h < 1 ∧
      (∀ i, |p i| < H) ∧ (∀ i, h ^ (p i) = x₀ i) ∧
      ∀ e, h ^ H * (∑ e, κ e) < κ e := by
  obtain ⟨h, hh, hh₀', hh1, hp, hrates⟩ :=
    exists_small_parameter (fun i => Real.log (x₀ i)) κ hH hh₀ hκ
  refine ⟨h, fun i => Real.log (x₀ i) / Real.log h, hh, hh₀', hh1, hp, ?_, hrates⟩
  intro i
  exact rpow_log_ratio hh hh1 (hx₀ i)

end Problem326

/-! Simultaneous small-parameter choice for the affine trapping construction. -/

namespace Problem326

open Filter Set
open scoped Topology

/-- The logarithmic exponent of a fixed coordinate tends to zero when the
base tends to zero from the right.  Positivity of the coordinate is not
needed for this limit (but is needed to reconstruct it from its exponent). -/
theorem tendsto_log_coordinate_div_log (x : ℝ) :
    Tendsto (fun h : ℝ => Real.log x / Real.log h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  Real.tendsto_log_nhdsGT_zero.const_div_atBot (Real.log x)

/-- A positive fixed power tends to zero, including on the positive side. -/
theorem tendsto_positive_rpow_nhdsGT_zero {H : ℝ} (hH : 0 < H) :
    Tendsto (fun h : ℝ => h ^ H) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [Real.zero_rpow hH.ne'] using
    (Real.continuousAt_rpow_const 0 H (Or.inr hH.le)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))

/-- Choose one small parameter after all slopes and their positive separation
have already been fixed.  All coordinate and reaction constraints hold
simultaneously; an empty reaction type causes no exceptional case. -/
theorem exists_small_parameter_for_rates
    {ι : Type uIota} {E : Type uE} [Finite ι] [Fintype E]
    (x0 : ι → ℝ) (κ : E → ℝ) {h0 H : ℝ}
    (hh0 : 0 < h0) (hH : 0 < H) (hκ : ∀ e, 0 < κ e) :
    ∃ h : ℝ, 0 < h ∧ h < h0 ∧ h < 1 ∧
      (∀ i, |Real.log (x0 i) / Real.log h| < H) ∧
      (∀ e, h ^ H * (∑ f, κ f) < κ e) := by
  have hcoords : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ∀ i, |Real.log (x0 i) / Real.log h| < H := by
    apply eventually_all.mpr
    intro i
    have hlim := (tendsto_log_coordinate_div_log (x0 i)).abs
    have hevent := hlim.eventually (Iio_mem_nhds (by simpa only [abs_zero] using hH))
    simpa only [abs_zero, mem_Iio] using hevent
  have hrates : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ∀ e, h ^ H * (∑ f, κ f) < κ e := by
    apply eventually_all.mpr
    intro e
    have hlim := (tendsto_positive_rpow_nhdsGT_zero hH).mul_const (∑ f, κ f)
    have hevent := hlim.eventually (Iio_mem_nhds (by simpa only [zero_mul] using hκ e))
    simpa only [zero_mul, mem_Iio] using hevent
  have hpositive : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < h0 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hh0)
  have hone : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  exact (hpositive.and (hsmall.and (hone.and (hcoords.and hrates)))).exists

/-- Positive coordinates are recovered exactly from their logarithmic
exponents for a base strictly between zero and one. -/
theorem rpow_log_coordinate {h x : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hx : 0 < x) :
    h ^ (Real.log x / Real.log h) = x := by
  simpa only [Real.logb] using Real.rpow_logb hh hh1.ne hx

/-- The open symmetric exponent interval describes the interior of the
positive reciprocal box in each coordinate. -/
theorem abs_log_coordinate_lt_one_iff {h x : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hx : 0 < x) :
    |Real.log x / Real.log h| < 1 ↔ h < x ∧ x < h⁻¹ := by
  rw [abs_lt]
  change (-1 < Real.logb h x ∧ Real.logb h x < 1) ↔ _
  rw [Real.lt_logb_iff_rpow_lt_of_base_lt_one hh hh1 hx,
    Real.logb_lt_iff_lt_rpow_of_base_lt_one hh hh1 hx]
  simp only [Real.rpow_neg_one, Real.rpow_one, and_comm]

/-- The closed symmetric exponent interval describes the closed positive
reciprocal box in each coordinate. -/
theorem abs_log_coordinate_le_one_iff {h x : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hx : 0 < x) :
    |Real.log x / Real.log h| ≤ 1 ↔ h ≤ x ∧ x ≤ h⁻¹ := by
  rw [abs_le]
  change (-1 ≤ Real.logb h x ∧ Real.logb h x ≤ 1) ↔ _
  rw [Real.le_logb_iff_rpow_le_of_base_lt_one hh hh1 hx,
    Real.logb_le_iff_le_rpow_of_base_lt_one hh hh1 hx]
  simp only [Real.rpow_neg_one, Real.rpow_one, and_comm]

end Problem326

end

end OAI
