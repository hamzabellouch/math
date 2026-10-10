import OAI.Probability.Renewal.Definitions

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace HoneycombLocal

lemma integrable_laplace (p : PMF ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Integrable (fun j : ℕ => Real.exp (-u * (j : ℝ))) p.toMeasure := by
  refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1 ?_
  filter_upwards [] with j
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (Nat.cast_nonneg _))

lemma laplace_pos (p : PMF ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 < laplace p u :=
  integral_exp_pos (integrable_laplace p hu)

lemma laplace_le_one (p : PMF ℕ) {u : ℝ} (hu : 0 ≤ u) : laplace p u ≤ 1 := by
  calc
    laplace p u ≤ ∫ _ : ℕ, (1 : ℝ) ∂p.toMeasure := by
      apply integral_mono (integrable_laplace p hu) (integrable_const 1)
      intro j
      exact Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
    _ = 1 := by simp

lemma integrable_deficit (p : PMF ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Integrable (fun j : ℕ => 1 - Real.exp (-u * (j : ℝ))) p.toMeasure :=
  (integrable_const 1).sub (integrable_laplace p hu)

lemma deficit_integral (p : PMF ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ j : ℕ, 1 - Real.exp (-u * (j : ℝ)) ∂p.toMeasure) = 1 - laplace p u := by
  rw [integral_sub (integrable_const 1) (integrable_laplace p hu)]
  simp [laplace]

lemma one_sub_exp_neg_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  linarith [Real.add_one_le_exp (-x)]

lemma one_sub_exp_neg_lower {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (-1) * s ≤ 1 - Real.exp (-s) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp s) (Real.exp_pos (-s)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have he : Real.exp (-1) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (neg_le_neg hs1)
  have hm := mul_le_mul_of_nonneg_right he hs
  nlinarith

lemma laplace_split_bound (p : PMF ℕ) {u y x : ℝ} (hu : 0 < u) (hy : 0 < y) :
    1 - laplace p u ≤ (u * y / Real.exp (-1)) * (1 - laplace p y⁻¹) +
      p.toMeasure.real {j | y < (j : ℝ) ∧ (j : ℝ) ≤ x} +
      p.toMeasure.real {j | x < (j : ℝ)} := by
  let K : ℝ := u * y / Real.exp (-1)
  let s : Set ℕ := {j | y < (j : ℝ) ∧ (j : ℝ) ≤ x}
  let b : Set ℕ := {j | x < (j : ℝ)}
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hc := integrable_deficit p (inv_nonneg.mpr hy.le)
  have hs : Integrable (s.indicator (fun _ => (1 : ℝ))) p.toMeasure :=
    (integrable_const 1).indicator MeasurableSet.of_discrete
  have hb : Integrable (b.indicator (fun _ => (1 : ℝ))) p.toMeasure :=
    (integrable_const 1).indicator MeasurableSet.of_discrete
  have hpt (j : ℕ) : 1 - Real.exp (-u * (j : ℝ)) ≤
      K * (1 - Real.exp (-y⁻¹ * (j : ℝ))) +
        s.indicator (fun _ => (1 : ℝ)) j + b.indicator (fun _ => (1 : ℝ)) j := by
    have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hdef : 0 ≤ 1 - Real.exp (-y⁻¹ * (j : ℝ)) := by
      have he : Real.exp (-y⁻¹ * (j : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (inv_nonneg.mpr hy.le)) hn)
      linarith
    have hsi : 0 ≤ s.indicator (fun _ => (1 : ℝ)) j := Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hbi : 0 ≤ b.indicator (fun _ => (1 : ℝ)) j := Set.indicator_nonneg (fun _ _ => zero_le_one) _
    by_cases hj : (j : ℝ) ≤ y
    · have hsmall : y⁻¹ * (j : ℝ) ≤ 1 := by
        rw [inv_mul_eq_div, div_le_one hy]; exact hj
      have hlo := one_sub_exp_neg_lower (mul_nonneg (inv_nonneg.mpr hy.le) hn) hsmall
      have hmul := mul_le_mul_of_nonneg_left hlo hK
      have hid : K * (Real.exp (-1) * (y⁻¹ * j)) = u * (j : ℝ) := by
        dsimp [K]; field_simp
      rw [hid] at hmul
      have hup := one_sub_exp_neg_le (u * j)
      simp only [neg_mul] at hlo hmul hup ⊢
      linarith
    · by_cases hjx : (j : ℝ) ≤ x
      · have hmem : j ∈ s := ⟨lt_of_not_ge hj, hjx⟩
        rw [Set.indicator_of_mem hmem]
        nlinarith [Real.exp_pos (-u * (j : ℝ)), mul_nonneg hK hdef]
      · have hmem : j ∈ b := lt_of_not_ge hjx
        rw [Set.indicator_of_mem hmem]
        nlinarith [Real.exp_pos (-u * (j : ℝ)), mul_nonneg hK hdef]
  have h := integral_mono (integrable_deficit p hu.le) ((hc.const_mul K).add hs |>.add hb) hpt
  have hsum : (∫ j : ℕ, K * (1 - Real.exp (-y⁻¹ * j)) +
      s.indicator (fun _ => (1 : ℝ)) j + b.indicator (fun _ => (1 : ℝ)) j ∂p.toMeasure) =
      (∫ j : ℕ, K * (1 - Real.exp (-y⁻¹ * j)) + s.indicator (fun _ => (1 : ℝ)) j ∂p.toMeasure) +
      ∫ j, b.indicator (fun _ => (1 : ℝ)) j ∂p.toMeasure := by
    simpa only [Pi.add_apply] using integral_add ((hc.const_mul K).add hs) hb
  have hsum' : (∫ j : ℕ, K * (1 - Real.exp (-y⁻¹ * j)) + s.indicator (fun _ => (1 : ℝ)) j ∂p.toMeasure) =
      (∫ j : ℕ, K * (1 - Real.exp (-y⁻¹ * j)) ∂p.toMeasure) +
      ∫ j, s.indicator (fun _ => (1 : ℝ)) j ∂p.toMeasure := by
    simpa only [Pi.add_apply] using integral_add (hc.const_mul K) hs
  simp only [Pi.add_apply] at h
  rw [deficit_integral p hu.le, hsum, hsum', integral_const_mul,
    deficit_integral p (inv_nonneg.mpr hy.le), integral_indicator MeasurableSet.of_discrete,
    integral_indicator MeasurableSet.of_discrete] at h
  simpa [K, s, b] using h

lemma annular_mass (p : PMF ℕ) {a : ℝ} (ha : 0 < a ∧ a < 1)
    (hpower : BoundedPowerInput p a) :
    ∃ M > (1 : ℝ), ∃ c₁ > (0 : ℝ), ∀ᶠ x : ℝ in atTop,
      c₁ * x ^ (-a) ≤ p.toMeasure.real {j | x / M < (j : ℝ) ∧ (j : ℝ) ≤ x} := by
  rcases hpower with ⟨c, hc, C, hC, x₀, hx₀, htail, hLap⟩
  have hAev : ∀ᶠ A : ℝ in atTop, 4 * C / c ≤ A ^ a :=
    (tendsto_rpow_atTop ha.1).eventually (eventually_ge_atTop _)
  obtain ⟨A, hA, hApow⟩ := ((eventually_gt_atTop (0 : ℝ)).and hAev).exists
  have hD : 0 < c * A ^ a := mul_pos hc (Real.rpow_pos_of_pos hA a)
  have hCA : 4 * C ≤ c * A ^ a := by
    have := (div_le_iff₀ hc).mp hApow
    nlinarith
  have hMlim : Tendsto (fun M : ℝ => C * A / Real.exp (-1) * M ^ (a - 1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (sub_pos.mpr ha.2)).const_mul (C * A / Real.exp (-1))
    simpa only [neg_sub, mul_zero] using this
  have hMev : ∀ᶠ M : ℝ in atTop,
      C * A / Real.exp (-1) * M ^ (a - 1) < c * A ^ a / 4 :=
    hMlim.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨M, hM, hMpow⟩ := ((eventually_gt_atTop (1 : ℝ)).and hMev).exists
  have hM0 : 0 < M := zero_lt_one.trans hM
  refine ⟨M, hM, c * A ^ a / 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop x₀, eventually_ge_atTop (A * x₀),
    eventually_ge_atTop (M * x₀)] with x hx hxA hxM
  have hxpos : 0 < x := hx₀.trans_le hx
  have hAu : A / x ≤ x₀⁻¹ := by
    rw [← one_div]
    apply (div_le_div_iff₀ hxpos hx₀).mpr
    simpa using hxA
  have hMu : M / x ≤ x₀⁻¹ := by
    rw [← one_div]
    apply (div_le_div_iff₀ hxpos hx₀).mpr
    simpa using hxM
  have hlow := (hLap (A / x) (div_pos hA hxpos) hAu).1
  have hup := (hLap (M / x) (div_pos hM0 hxpos) hMu).2
  have hsplit := laplace_split_bound p (x := x) (div_pos hA hxpos) (div_pos hxpos hM0)
  have hinv : (x / M)⁻¹ = M / x := by field_simp
  rw [hinv] at hsplit
  have halg : c * (A / x) ^ a = c * A ^ a * x ^ (-a) := by
    rw [Real.div_rpow hA.le hxpos.le, Real.rpow_neg hxpos.le]
    ring
  rw [halg] at hlow
  have hcoef : 0 ≤ (A / x) * (x / M) / Real.exp (-1) := by positivity
  have hup' := mul_le_mul_of_nonneg_left hup hcoef
  have halg' : (A / x * (x / M) / Real.exp (-1)) * (C * (M / x) ^ a) =
      (C * A / Real.exp (-1) * M ^ (a - 1)) * x ^ (-a) := by
    rw [Real.div_rpow hM0.le hxpos.le, Real.rpow_sub hM0, Real.rpow_one,
      Real.rpow_neg hxpos.le]
    field_simp
  rw [halg'] at hup'
  have hscale : 0 ≤ x ^ (-a) := Real.rpow_nonneg hxpos.le _
  have hms := mul_le_mul_of_nonneg_right hMpow.le hscale
  have hts := htail x hx
  have hcs := mul_le_mul_of_nonneg_right hCA hscale
  nlinarith

end HoneycombLocal

end

end OAI
