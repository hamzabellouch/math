import Mathlib
import OAI.Geometry.CubicTorus.Profiles.AtanPoly

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Shape

lemma shape_nonneg {q : ℝ} (hq : q ∈ Icc 0 1) : 0 ≤ shape q := by
  exact le_min (sq_nonneg q) (div_nonneg
    (mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.2 hq.2)) (by norm_num [c, dm]))

lemma shape_le_one {q : ℝ} (hq : q ∈ Icc 0 1) : shape q ≤ 1 := by
  have hq2 := pow_le_pow_left₀ hq.1 hq.2 2
  exact le_trans (min_le_left _ _) (by simpa using hq2)

lemma shape_max {q : ℝ} (hq : q ∈ Icc 0 1) : shape q ≤ theta ^ 2 := by
  by_cases hh : q ≤ theta
  · rw [shape_on_left ⟨hq.1, hh⟩]
    exact pow_le_pow_left₀ hq.1 hh 2
  · rw [shape_on_right ⟨le_of_not_ge hh, hq.2⟩]
    apply (div_le_iff₀ (by norm_num [c, dm] : 0 < c * dm)).2
    have ht := theta_spec.2.2
    have hp := mul_le_mul_of_nonneg_left (le_of_not_ge hh) (le_of_lt Real.pi_pos)
    nlinarith

lemma continuous_shape : Continuous shape := by
  unfold shape
  fun_prop

lemma integral_eq_split : moment = theta ^ 3 / 3 +
    Real.pi / (c * dm) * (1 - theta) ^ 2 / 2 := by
  have hfi : IntervalIntegrable shape volume 0 theta := continuous_shape.intervalIntegrable 0 theta
  have hfi2 : IntervalIntegrable shape volume theta 1 := continuous_shape.intervalIntegrable theta 1
  have h0 := theta_spec
  unfold moment
  rw [← intervalIntegral.integral_add_adjacent_intervals hfi hfi2]
  have hleft : (∫ q in (0 : ℝ)..theta, shape q) = theta ^ 3 / 3 := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => q ^ 2) ?_]
    · norm_num
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.1)] at hq
      exact shape_on_left hq
  have hright : (∫ q in theta..(1 : ℝ), shape q) =
      Real.pi / (c * dm) * (1 - theta) ^ 2 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => Real.pi / (c * dm) * (1 - q)) ?_]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (show IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume theta 1 from continuous_const.intervalIntegrable _ _)
          (show IntervalIntegrable (fun q : ℝ => q) volume theta 1 from continuous_id.intervalIntegrable _ _)]
      norm_num
      ring
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.2.1)] at hq
      dsimp only
      rw [shape_on_right hq]
      ring
  rw [hleft, hright]

lemma moment_eq : moment = theta ^ 2 * (3 - theta) / 6 := by
  rw [integral_eq_split]
  have ht := theta_spec.2.2
  norm_num [c, dm] at ht ⊢
  linear_combination -(500 / 567 : ℝ) * (1 - theta) * ht

lemma firstMoment_eq : firstMoment = theta ^ 2 * (2 + 2 * theta - theta ^ 2) / 12 := by
  have hc : Continuous (fun q : ℝ => q * shape q) := continuous_id.mul continuous_shape
  have h0 := theta_spec
  unfold firstMoment
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (0 : ℝ) theta) (hc.intervalIntegrable theta (1 : ℝ))]
  have hl : (∫ q in (0 : ℝ)..theta, q * shape q) = theta ^ 4 / 4 := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => q ^ 3) ?_]
    · norm_num
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.1)] at hq
      dsimp only
      rw [shape_on_left hq]
      ring
  have hr : (∫ q in theta..(1 : ℝ), q * shape q) =
      Real.pi / (c * dm) * ((1 - theta ^ 2) / 2 - (1 - theta ^ 3) / 3) := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => Real.pi / (c * dm) * (q - q ^ 2)) ?_]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (show IntervalIntegrable (fun q : ℝ => q) volume theta 1 from continuous_id.intervalIntegrable _ _)
          (show IntervalIntegrable (fun q : ℝ => q ^ 2) volume theta 1 from (continuous_id.pow 2).intervalIntegrable _ _)]
      norm_num
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.2.1)] at hq
      dsimp only
      rw [shape_on_right hq]
      ring
  rw [hl, hr]
  have ht := h0.2.2
  norm_num [c, dm] at ht ⊢
  linear_combination -(500 / 1701 : ℝ) * (1 - theta) * (1 + 2 * theta) * ht

lemma moment_pos : 0 < moment := by
  rw [moment_eq]
  have ht := theta_spec
  have h3 : 0 < 3 - theta := by linarith [ht.2.1]
  have htpos := ht.1
  positivity

lemma meanQ_eq : meanQ = (2 + 2 * theta - theta ^ 2) / (2 * (3 - theta)) := by
  unfold meanQ
  rw [moment_eq, firstMoment_eq]
  have ht := theta_spec
  have ht0 := ne_of_gt ht.1
  have h30 : 3 - theta ≠ 0 := by linarith [ht.2.1]
  field_simp [ht0, h30]
  ring

lemma meanQ_mem : meanQ ∈ Ioo 0 1 := by
  rw [meanQ_eq]
  have ht := theta_spec
  have hs : theta ^ 2 < 1 := by nlinarith [ht.1, ht.2.1]
  constructor
  · apply div_pos
    · nlinarith
    · linarith
  · apply (div_lt_one (by linarith : 0 < 2 * (3 - theta))).2
    nlinarith [sq_nonneg (theta - 2)]

theorem moment_bounds : (2659 / 10000 : ℝ) < moment ∧
    (697 / 1000 : ℝ) < meanQ ∧ p₂ < (109 / 100 : ℝ) := by
  have ht := theta_spec
  have hb := theta_bounds
  have hθ2 := pow_lt_pow_left₀ hb.1 (by norm_num : (0 : ℝ) ≤ 32 / 37) (by norm_num : (2 : ℕ) ≠ 0)
  have hθU := pow_lt_pow_left₀ hb.2 (le_of_lt ht.1) (by norm_num : (2 : ℕ) ≠ 0)
  refine ⟨?_, ?_, ?_⟩
  · rw [moment_eq]
    have hm : 0 ≤ (theta ^ 2 - (32 / 37) ^ 2) * (3 - theta) :=
      mul_nonneg (by linarith) (by linarith [ht.2.1])
    nlinarith [hb.2]
  · rw [meanQ_eq]
    apply (lt_div_iff₀ (by linarith : 0 < 2 * (3 - theta))).2
    nlinarith [sq_nonneg (theta - 1)]
  · dsimp [p₂, c, dm]
    nlinarith

lemma affine_shape_integral (a b : ℝ) :
    (∫ q in (0 : ℝ)..1, (a + b * q) * shape q) = moment * (a + b * meanQ) := by
  have hc : IntervalIntegrable shape volume 0 1 := continuous_shape.intervalIntegrable 0 1
  have hq : IntervalIntegrable (fun q : ℝ => q * shape q) volume 0 1 :=
    (continuous_id.mul continuous_shape).intervalIntegrable 0 1
  have heq : (fun q : ℝ => (a + b * q) * shape q) =
      fun q => a * shape q + b * (q * shape q) := by funext q; ring
  rw [heq, intervalIntegral.integral_add (hc.const_mul a) (hq.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change a * moment + b * firstMoment = moment * (a + b * meanQ)
  unfold meanQ
  field_simp [ne_of_gt moment_pos]

lemma cubic_shape_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moment * (a + b * meanQ) ^ 3 ≤
      ∫ q in (0 : ℝ)..1, (a + b * q) ^ 3 * shape q := by
  let m := a + b * meanQ
  have hm : 0 ≤ m := add_nonneg ha (mul_nonneg hb (le_of_lt meanQ_mem.1))
  have hc : IntervalIntegrable (fun q : ℝ => (a + b * q) ^ 3 * shape q) volume 0 1 :=
    (((continuous_const.add (continuous_const.mul continuous_id)).pow 3).mul continuous_shape).intervalIntegrable 0 1
  have h1 : IntervalIntegrable (fun q : ℝ => m ^ 3 * shape q) volume 0 1 :=
    (continuous_const.mul continuous_shape).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun q : ℝ => (a + b * q - m) * shape q) volume 0 1 :=
    (( (continuous_const.add (continuous_const.mul continuous_id)).sub continuous_const).mul continuous_shape).intervalIntegrable 0 1
  have hbound := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    (h1.add (h2.const_mul (3 * m ^ 2))) hc (fun q hq => by
      have hs := shape_nonneg hq
      have hf : 0 ≤ a + b * q := add_nonneg ha (mul_nonneg hb hq.1)
      have hh := mul_nonneg (mul_nonneg (sq_nonneg (a + b * q - m))
        (show 0 ≤ a + b * q + 2 * m by linarith)) hs
      nlinarith)
  rw [intervalIntegral.integral_add h1 (h2.const_mul (3 * m ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hbound
  have hz : (∫ q in (0 : ℝ)..1, (a + b * q - m) * shape q) = 0 := by
    have heq : (fun q : ℝ => (a + b * q - m) * shape q) =
        fun q => (a - m + b * q) * shape q := by funext q; ring
    rw [heq, affine_shape_integral]
    dsimp [m]
    ring
  rw [hz, mul_zero, add_zero] at hbound
  change moment * m ^ 3 ≤ _
  change m ^ 3 * moment ≤ _ at hbound
  linarith only [hbound]

lemma cubic_shape_lower_dm {u₀ δ : ℝ} (hδ : δ ∈ Icc 0 dm) (hu : dm ≤ u₀) :
    moment * (u₀ - (1 - meanQ) * dm) ^ 3 ≤
      ∫ q in (0 : ℝ)..1, (u₀ - δ + δ * q) ^ 3 * shape q := by
  have hm := meanQ_mem
  have h1 := cubic_shape_lower (a := u₀ - δ) (b := δ) (by linarith [hδ.2]) hδ.1
  apply le_trans _ h1
  apply mul_le_mul_of_nonneg_left _ (le_of_lt moment_pos)
  have hb : u₀ - (1 - meanQ) * dm ≤ u₀ - δ + δ * meanQ := by
    have hh := mul_le_mul_of_nonneg_left hδ.2 (show 0 ≤ 1 - meanQ by linarith [hm.2])
    nlinarith
  apply pow_le_pow_left₀ _ hb 3
  have hh : 0 ≤ dm * meanQ := mul_nonneg (by norm_num [dm]) (le_of_lt hm.1)
  nlinarith

lemma p₂_pos : 0 < p₂ := by
  unfold p₂ c dm
  positivity

lemma coefficient_lower : (574 / 1000 : ℝ) <
    ((91 / 100 : ℝ) * c * moment) / Real.sqrt p₂ ^ 3 := by
  have hM := moment_bounds.1
  have hp := moment_bounds.2.2
  have hs : 0 < Real.sqrt p₂ := Real.sqrt_pos.2 p₂_pos
  have hs2 := Real.sq_sqrt (le_of_lt p₂_pos)
  have hd : (Real.sqrt p₂ ^ 3) ^ 2 = p₂ ^ 3 := by
    rw [show (Real.sqrt p₂ ^ 3) ^ 2 = (Real.sqrt p₂ ^ 2) ^ 3 by ring, hs2]
  have hp3 := pow_lt_pow_left₀ hp (le_of_lt p₂_pos) (by norm_num : (3 : ℕ) ≠ 0)
  have hc : (574 / 1000 : ℝ) * Real.sqrt p₂ ^ 3 <
      (91 / 100 : ℝ) * c * (2659 / 10000 : ℝ) := by
    apply (sq_lt_sq₀ (by positivity)
      (by norm_num [c] : (0 : ℝ) ≤ (91 / 100 : ℝ) * c * (2659 / 10000 : ℝ))).1
    rw [mul_pow, hd]
    norm_num [c]
    nlinarith only [hp3]
  apply (lt_div_iff₀ (pow_pos hs 3)).2
  have hmc := mul_lt_mul_of_pos_left hM (by norm_num [c] : (0 : ℝ) < (91 / 100 : ℝ) * c)
  exact lt_trans hc hmc

theorem uniform_coefficient {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    min ((134 / 1000 : ℝ) * h ^ 3) (36 / 100 : ℝ) ≤
      ((91 / 100 : ℝ) * c * moment / Real.sqrt p₂ ^ 3) *
        (h * (u h - (1 - meanQ) * dm)) ^ 3 := by
  let d₀ : ℝ := (1 - meanQ) * dm
  have hd0 : 0 ≤ d₀ := mul_nonneg (by linarith [meanQ_mem.2]) (by norm_num [dm])
  have hd : d₀ ≤ (6363 / 100000 : ℝ) := by
    dsimp [d₀, dm]
    linarith [moment_bounds.2.1]
  have hh0 : 0 < h := by linarith [hh.1]
  have hc := coefficient_lower
  by_cases hbranch : 1 - 1 / Real.pi ≤ (24 / 25 : ℝ) / h
  · have hip : 1 / Real.pi ≤ (1 / (314 / 100) : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [Real.pi_gt_d2])
    have hb : (617 / 1000 : ℝ) ≤ 1 - 1 / Real.pi - d₀ := by linarith
    have hbase : (617 / 1000 : ℝ) * h ≤ h * (u h - d₀) := by
      dsimp [u]
      rw [min_eq_left hbranch]
      nlinarith [mul_le_mul_of_nonneg_left hb (le_of_lt hh0)]
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (617 / 1000 : ℝ) * h) hbase 3
    have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 574 / 1000)
    have hmc := mul_le_mul_of_nonneg_right (le_of_lt hc)
      (pow_nonneg (le_trans (by positivity : (0 : ℝ) ≤ (617 / 1000 : ℝ) * h) hbase) 3)
    apply le_trans (min_le_left _ _) _
    change (134 / 1000 : ℝ) * h ^ 3 ≤ _ * (h * (u h - d₀)) ^ 3
    nlinarith only [hm, hmc, pow_pos hh0 3]
  · have hbranch' : (24 / 25 : ℝ) / h ≤ 1 - 1 / Real.pi := le_of_not_ge hbranch
    have hprod : h * d₀ ≤ (81 / 50 : ℝ) * (6363 / 100000 : ℝ) :=
      mul_le_mul hh.2 hd hd0 (by norm_num)
    have hbase : (856 / 1000 : ℝ) ≤ h * (u h - d₀) := by
      dsimp [u]
      rw [min_eq_right hbranch']
      have heq : h * ((24 / 25 : ℝ) / h - d₀) = 24 / 25 - h * d₀ := by
        field_simp
      rw [heq]
      linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 856 / 1000) hbase 3
    have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 574 / 1000)
    have hmc := mul_le_mul_of_nonneg_right (le_of_lt hc)
      (pow_nonneg (by linarith : 0 ≤ h * (u h - d₀)) 3)
    apply le_trans (min_le_right _ _) _
    change (36 / 100 : ℝ) ≤ _ * (h * (u h - d₀)) ^ 3
    nlinarith only [hm, hmc]

end CubicTorus.Shape

namespace CubicTorus.NestingGain
open _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma continuousOn_weight : ContinuousOn weight (Ici 0) := by
  exact Nesting.continuousOn_rawWeight.comp
    (continuous_id.min continuous_const).continuousOn
    (fun x hx => ⟨le_min hx (le_of_lt cutoff_pos), min_le_right _ _⟩)

lemma nesting_parameters {h δ q : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
    (hδ : δ ∈ Icc 0 dm) (hq : q ∈ Icc 0 1) :
    h * (u h - δ + δ * q) ∈ Icc 0 (24 / 25 : ℝ) ∧
      0 ≤ c * δ ^ 2 * shape q ∧ 1 + c * δ ^ 2 * shape q ≤ p₂ := by
  have hu := interval_placement hh
  have hh0 : 0 ≤ h := by linarith [hh.1]
  have hv0 : 0 ≤ u h - δ + δ * q := by
    have := mul_nonneg hδ.1 hq.1
    linarith [hu.2.1, hδ.2]
  have hv1 : u h - δ + δ * q ≤ u h := by
    have := mul_le_mul_of_nonneg_left hq.2 hδ.1
    linarith
  have hK0 : 0 ≤ c * δ ^ 2 * shape q := by
    exact mul_nonneg (mul_nonneg (by norm_num [c]) (sq_nonneg δ)) (shape_nonneg hq)
  have hK1 : c * δ ^ 2 * shape q ≤ c * dm ^ 2 * theta ^ 2 := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hδ.1 hδ.2 2) (by norm_num [c])) (shape_max hq)
      (shape_nonneg hq) (by norm_num [c, dm])
  exact ⟨⟨mul_nonneg hh0 hv0,
    le_trans (mul_le_mul_of_nonneg_left hv1 hh0) hu.2.2.2.2.2⟩,
    hK0, by dsimp [p₂]; linarith⟩

lemma pointwise_uniform_gain {h δ q : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
    (hδ : δ ∈ Icc 0 dm) (hq : q ∈ Icc 0 1) :
    ((91 / 100 : ℝ) * c * δ ^ 2 * h ^ 3 / Real.sqrt p₂ ^ 3) *
        ((u h - δ + δ * q) ^ 3 * shape q) ≤
      weight ((h * (u h - δ + δ * q)) / Real.sqrt (1 + c * δ ^ 2 * shape q)) -
        weight (h * (u h - δ + δ * q)) := by
  have hp := nesting_parameters hh hδ hq
  have hlow := pointwise_weight_gain hp.1 hp.2.1
  apply le_trans _ hlow
  have hnum : 0 ≤ (91 / 100 : ℝ) * (h * (u h - δ + δ * q)) ^ 3 *
      (c * δ ^ 2 * shape q) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp.1.1 3)) hp.2.1
  have hden : (Real.sqrt (1 + c * δ ^ 2 * shape q)) ^ 3 ≤ Real.sqrt p₂ ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hp.2.2) 3
  have hden0 : 0 < (Real.sqrt (1 + c * δ ^ 2 * shape q)) ^ 3 := by
    apply pow_pos
    apply Real.sqrt_pos.2
    linarith [hp.2.1]
  convert div_le_div_of_nonneg_left hnum hden0 hden using 1
  ring

theorem integrated_uniform_gain {h δ : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) (hδ : δ ∈ Icc 0 dm) :
    min ((134 / 1000 : ℝ) * h ^ 3) (36 / 100 : ℝ) * δ ^ 3 ≤
      δ * ∫ q in (0 : ℝ)..1,
        (weight ((h * (u h - δ + δ * q)) / Real.sqrt (1 + c * δ ^ 2 * shape q)) -
          weight (h * (u h - δ + δ * q))) := by
  let v : ℝ → ℝ := fun q => u h - δ + δ * q
  let K : ℝ → ℝ := fun q => c * δ ^ 2 * shape q
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hK : Continuous K := by dsimp [K]; exact continuous_const.mul continuous_shape
  have hc1 : ContinuousOn (fun q => weight ((h * v q) / Real.sqrt (1 + K q))) (Icc 0 1) := by
    apply continuousOn_weight.comp
    · apply (continuous_const.mul hv).continuousOn.div
        (Real.continuous_sqrt.comp (continuous_const.add hK)).continuousOn
      intro q hq
      exact ne_of_gt (Real.sqrt_pos.2 (by
        change 0 < 1 + c * δ ^ 2 * shape q
        linarith [(nesting_parameters hh hδ hq).2.1]))
    · intro q hq
      exact div_nonneg (nesting_parameters hh hδ hq).1.1 (Real.sqrt_nonneg _)
  have hc2 : ContinuousOn (fun q => weight (h * v q)) (Icc 0 1) :=
    continuousOn_weight.comp (continuous_const.mul hv).continuousOn
      (fun q hq => (nesting_parameters hh hδ hq).1.1)
  have hright : IntervalIntegrable (fun q => weight ((h * v q) / Real.sqrt (1 + K q)) -
      weight (h * v q)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (hc1.sub hc2)
  let A : ℝ := (91 / 100 : ℝ) * c * δ ^ 2 * h ^ 3 / Real.sqrt p₂ ^ 3
  have hleft : IntervalIntegrable (fun q => A * (v q ^ 3 * shape q)) volume 0 1 :=
    (continuous_const.mul ((hv.pow 3).mul continuous_shape)).intervalIntegrable 0 1
  have hmon := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    hleft hright (fun q hq => pointwise_uniform_gain hh hδ hq)
  rw [intervalIntegral.integral_const_mul] at hmon
  have hA : 0 ≤ A := by
    have hh0 : 0 ≤ h := by linarith [hh.1]
    dsimp [A, c]
    positivity
  have hu : dm ≤ u h := by linarith [(interval_placement hh).2.1]
  have hcubic := mul_le_mul_of_nonneg_left (cubic_shape_lower_dm hδ hu) hA
  have hδlower := mul_le_mul_of_nonneg_left (le_trans hcubic hmon) hδ.1
  have hcoeff := mul_le_mul_of_nonneg_right (uniform_coefficient hh) (pow_nonneg hδ.1 3)
  apply le_trans hcoeff
  convert hδlower using 1
  dsimp [A, v, K]
  ring

end CubicTorus.NestingGain

namespace CubicTorus.Scalar
open Set MeasureTheory
open _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def planarProfile (v : ℝ) : ℝ :=
  min (Real.sqrt (Real.pi * v)) (min 1 (Real.sqrt (Real.pi * (1 - v))))

def baseline (h : ℝ) : ℝ :=
  lambda * h / Real.pi + (∫ v in (0 : ℝ)..t h, weight (h * v / planarProfile v)) - 1

def P (h : ℝ) : ℝ := u h - 1 + 2 * h * t h / Real.pi

def Q (h : ℝ) : ℝ := 2 / Real.pi * Real.sqrt (Real.pi + 2 * h ^ 2 * t h)

def C₀ (h : ℝ) : ℝ := min ((67 / 500 : ℝ) * h ^ 3) (9 / 25)

def cappedEnergy (l a d p q y : ℝ) : ℝ :=
  l * y ^ 2 + a * min d (max (p - q * y) 0) ^ 3

def cappedInf (l a d p q : ℝ) : ℝ :=
  sInf ((cappedEnergy l a d p q) '' Ici 0)

def gain (h : ℝ) : ℝ := cappedInf ell (C₀ h) dm (P h) (Q h)

def critical (l a p q : ℝ) : ℝ :=
  2 * p / (1 + Real.sqrt (1 + 6 * a * q ^ 2 * p / l))

lemma critical_spec {l a p q : ℝ} (hl : 0 < l) (ha : 0 < a) (hp : 0 < p)
    (hq : q ≠ 0) :
    0 < critical l a p q ∧ critical l a p q < p ∧
      3 * a * q ^ 2 * (critical l a p q) ^ 2 = 2 * l * (p - critical l a p q) := by
  have hz : 0 < 6 * a * q ^ 2 * p / l := by positivity
  have hs0 := Real.sqrt_nonneg (1 + 6 * a * q ^ 2 * p / l)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 6 * a * q ^ 2 * p / l)
  have hs1 : 1 < Real.sqrt (1 + 6 * a * q ^ 2 * p / l) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + 6 * a * q ^ 2 * p / l) := by linarith
  unfold critical
  refine ⟨div_pos (by positivity) hd, (div_lt_iff₀ hd).2 (by nlinarith), ?_⟩
  generalize hx : Real.sqrt (1 + 6 * a * q ^ 2 * p / l) = x at *
  field_simp at hs ⊢
  nlinarith

lemma cubic_energy_min {l a p q r w : ℝ} (hl : 0 ≤ l) (ha : 0 ≤ a)
    (hq : q ≠ 0) (hr : 0 ≤ r) (hw : 0 ≤ w)
    (hcrit : 3 * a * q ^ 2 * r ^ 2 = 2 * l * (p - r)) :
    l * ((p - r) / q) ^ 2 + a * r ^ 3 ≤ l * ((p - w) / q) ^ 2 + a * w ^ 3 := by
  have hq2 : 0 < q ^ 2 := sq_pos_of_ne_zero hq
  have hpoly : 0 ≤ (w - r) ^ 2 * (l + a * q ^ 2 * (w + 2 * r)) := by positivity
  have hid : (w - r) ^ 2 * (l + a * q ^ 2 * (w + 2 * r)) =
      l * (p - w) ^ 2 + a * q ^ 2 * w ^ 3 - (l * (p - r) ^ 2 + a * q ^ 2 * r ^ 3) := by
    linear_combination -(w - r) * hcrit
  rw [hid] at hpoly
  apply (mul_le_mul_iff_of_pos_right hq2).mp
  have heq (z : ℝ) : (l * ((p - z) / q) ^ 2 + a * z ^ 3) * q ^ 2 =
      l * (p - z) ^ 2 + a * q ^ 2 * z ^ 3 := by field_simp [hq]
  rw [heq r, heq w]
  linarith

lemma cappedEnergy_nonneg {l a d p q y : ℝ} (hl : 0 ≤ l) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    0 ≤ cappedEnergy l a d p q y := by
  unfold cappedEnergy
  positivity

lemma cappedInf_formula {l a d p q : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hd : 0 ≤ d) (hp : 0 < p) (hq : 0 < q) :
    cappedInf l a d p q =
      min (a * d ^ 3) (l * ((p - critical l a p q) / q) ^ 2 + a * (critical l a p q) ^ 3) := by
  let r := critical l a p q
  change cappedInf l a d p q = min (a * d ^ 3) (l * ((p - r) / q) ^ 2 + a * r ^ 3)
  obtain ⟨hr, hrp, hcrit⟩ := critical_spec hl ha hp hq.ne'
  change 0 < r at hr
  change r < p at hrp
  change 3 * a * q ^ 2 * r ^ 2 = 2 * l * (p - r) at hcrit
  have hmin (w : ℝ) (hw : 0 ≤ w) := cubic_energy_min hl.le ha.le hq.ne' hr.le hw hcrit
  have hbdd : BddBelow ((cappedEnergy l a d p q) '' Ici 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact cappedEnergy_nonneg hl.le ha.le hd
  have hmem (y : ℝ) (hy : 0 ≤ y) : cappedEnergy l a d p q y ∈
      (cappedEnergy l a d p q) '' Ici 0 := ⟨y, hy, rfl⟩
  apply le_antisymm
  · apply le_min
    · apply (csInf_le hbdd (hmem 0 le_rfl)).trans
      simp only [cappedEnergy, mul_zero, sub_zero, sq, zero_add]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min hd (le_max_right _ _)) (min_le_left _ _) _) ha.le
    · have hy : 0 ≤ (p - r) / q := div_nonneg (by linarith) hq.le
      apply (csInf_le hbdd (hmem _ hy)).trans
      have heq : p - q * ((p - r) / q) = r := by field_simp; ring
      simp only [cappedEnergy, heq, max_eq_left hr.le]
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min hd hr.le) (min_le_right _ _) _) ha.le
  · apply le_csInf ⟨_, hmem 0 le_rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    by_cases hcap : d ≤ max (p - q * y) 0
    · apply (min_le_left _ _).trans
      simp only [cappedEnergy, min_eq_left hcap]
      nlinarith [sq_nonneg y]
    · have hun : min d (max (p - q * y) 0) = max (p - q * y) 0 := min_eq_right (le_of_not_ge hcap)
      apply (min_le_right _ _).trans
      by_cases hw : 0 ≤ p - q * y
      · have heq : (p - (p - q * y)) / q = y := by field_simp; ring
        rw [cappedEnergy, hun, max_eq_left hw]
        simpa only [heq] using hmin (p - q * y) hw
      · have hw' : p - q * y ≤ 0 := (lt_of_not_ge hw).le
        have hy' : p / q ≤ y := (div_le_iff₀ hq).2 (by nlinarith)
        have hpq : 0 ≤ p / q := by positivity
        have hh := mul_le_mul_of_nonneg_left (sq_le_sq₀ hpq hy |>.2 hy') hl.le
        have hm := hmin 0 le_rfl
        simp only [sub_zero, zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero] at hm
        rw [cappedEnergy, hun, max_eq_right hw']
        simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero] using hm.trans hh

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma gain_parameters_pos {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    0 < P h ∧ 0 < Q h ∧ 0 < C₀ h := by
  have hh0 : 0 < h := by linarith [hh.1]
  obtain ⟨ht0, ht1, ht⟩ := t_spec hh0
  have hht0 : 0 < h * t h := by positivity
  have hhtt : t h ≤ h * t h := by nlinarith [hh.1]
  have hht : (3 / 4 : ℝ) < h * t h := by
    by_contra! hn
    have hs := pow_le_pow_left₀ hht0.le hn 2
    have ht' : (h * t h) ^ 2 = Real.pi * (1 - t h) := by nlinarith only [ht]
    nlinarith [Real.pi_gt_three]
  have hu : (16 / 27 : ℝ) ≤ u h := by
    have := (interval_placement hh).1
    norm_num [dm] at this
    linarith
  have hR : (21 / 44 : ℝ) < 2 * h * t h / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).2
    have hπ : Real.pi < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold P
    linarith
  · unfold Q
    positivity
  · unfold C₀
    exact lt_min (by positivity) (by norm_num)

theorem gain_formula {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    gain h = min (C₀ h * dm ^ 3)
      (ell * ((P h - critical ell (C₀ h) (P h) (Q h)) / Q h) ^ 2 +
        C₀ h * (critical ell (C₀ h) (P h) (Q h)) ^ 3) := by
  obtain ⟨hp, hq, hc⟩ := gain_parameters_pos hh
  exact cappedInf_formula (by norm_num [ell]) hc (by norm_num [dm]) hp hq

lemma gain_nonneg {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    0 ≤ gain h := by
  rw [gain_formula hh]
  obtain ⟨hp, hq, hc⟩ := gain_parameters_pos hh
  have hr := (critical_spec (by norm_num [ell] : 0 < ell) hc hp hq.ne').1
  have hd : 0 ≤ dm := by norm_num [dm]
  have hl : 0 ≤ ell := by norm_num [ell]
  exact le_min (by positivity) (by positivity)

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def rho (k : ℝ) : ℝ :=
  Real.sqrt Real.pi * k * Real.sqrt (1 + (Real.pi / 4) * k ^ 2) - (Real.pi / 2) * k ^ 2

lemma nonneg_quadratic_sublevel {a r v : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hv : 0 ≤ v)
    (heq : r ^ 2 = a * (1 - r)) :
    v ^ 2 ≤ a * (1 - v) ↔ v ≤ r := by
  constructor
  · intro hn
    by_contra! hrv
    have hs := (sq_lt_sq₀ hr hv).2 hrv
    have hm := mul_le_mul_of_nonneg_left hrv.le ha
    nlinarith
  · intro hvr
    have hs := (sq_le_sq₀ hv hr).2 hvr
    have hm := mul_le_mul_of_nonneg_left hvr ha
    nlinarith

lemma rho_spec {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ rho k ∧ rho k < 1 ∧ (rho k) ^ 2 = Real.pi * k ^ 2 * (1 - rho k) := by
  let x := Real.sqrt Real.pi * k
  let z := Real.sqrt (1 + (Real.pi / 4) * k ^ 2)
  have hx : 0 ≤ x := by positivity
  have hx2 : x ^ 2 = Real.pi * k ^ 2 := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  have hz : 0 ≤ z := by positivity
  have hz2 : z ^ 2 = 1 + x ^ 2 / 4 := by
    dsimp [z]
    rw [Real.sq_sqrt (by positivity), hx2]
    ring
  have hzx : x / 2 < z := by nlinarith
  have heq : rho k = x * z - x ^ 2 / 2 := by
    dsimp [rho, x, z]
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
    ring
  have hr : 0 ≤ rho k := by rw [heq]; nlinarith
  have hs : (rho k) ^ 2 = Real.pi * k ^ 2 * (1 - rho k) := by
    rw [heq, ← hx2]
    linear_combination x ^ 2 * hz2
  refine ⟨hr, ?_, hs⟩
  by_contra! hn
  have hm := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ Real.pi * k ^ 2) (by linarith : 1 - rho k ≤ 0)
  nlinarith

lemma rho_pos {k : ℝ} (hk : 0 < k) : 0 < rho k := by
  obtain ⟨hr, _, hs⟩ := rho_spec hk.le
  have ha : 0 < Real.pi * k ^ 2 := by positivity
  by_contra! hn
  have heq : rho k = 0 := le_antisymm hn hr
  rw [heq] at hs
  norm_num at hs
  linarith

lemma rho_zero : rho 0 = 0 := by simp [rho]

lemma monotoneOn_rho : MonotoneOn rho (Ici 0) := by
  intro k hk K hK hkK
  obtain ⟨hr, hr1, hs⟩ := rho_spec hk
  obtain ⟨hR, _, hS⟩ := rho_spec hK
  apply (nonneg_quadratic_sublevel (by positivity : 0 ≤ Real.pi * K ^ 2) hR hr hS).1
  rw [hs]
  have hh := (sq_le_sq₀ hk hK).2 hkK
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh Real.pi_pos.le) (by linarith)

lemma rho_inverse_sublevel {v k : ℝ} (hv : v ∈ Ico 0 1) (hk : 0 ≤ k) :
    v / Real.sqrt (Real.pi * (1 - v)) ≤ k ↔ v ≤ rho k := by
  have hv1 : 0 < 1 - v := sub_pos.2 hv.2
  have hden : 0 < Real.sqrt (Real.pi * (1 - v)) := Real.sqrt_pos.2 (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ Real.pi * (1 - v) by positivity)
  rw [div_le_iff₀ hden]
  rw [← sq_le_sq₀ hv.1 (mul_nonneg hk hden.le)]
  rw [mul_pow, hs]
  have heq : k ^ 2 * (Real.pi * (1 - v)) = Real.pi * k ^ 2 * (1 - v) := by ring
  rw [heq]
  exact nonneg_quadratic_sublevel (by positivity : 0 ≤ Real.pi * k ^ 2)
    (rho_spec hk).1 hv.1 (rho_spec hk).2.2

lemma rho_at_inverse {h : ℝ} (hh : 0 < h) : rho (1 / h) = t h := by
  obtain ⟨ht, ht1, hs⟩ := t_spec hh
  obtain ⟨hr, _, hrs⟩ := rho_spec (show 0 ≤ (1 : ℝ) / h by positivity)
  have hts : (t h) ^ 2 = Real.pi * (1 / h) ^ 2 * (1 - t h) := by
    field_simp
    nlinarith only [hs]
  apply le_antisymm
  · exact (nonneg_quadratic_sublevel (by positivity) ht.le hr hts).1 hrs.le
  · exact (nonneg_quadratic_sublevel (by positivity) hr ht.le hrs).1 hts.le

lemma antitoneOn_t : AntitoneOn t (Ioi 0) := by
  intro h hh H hH hhH
  change 0 < h at hh
  change 0 < H at hH
  rw [← rho_at_inverse hh, ← rho_at_inverse hH]
  exact monotoneOn_rho (show 0 ≤ (1 : ℝ) / H by positivity) (show 0 ≤ (1 : ℝ) / h by positivity)
    (div_le_div_of_nonneg_left (by norm_num) hh hhH)

lemma monotoneOn_ht : MonotoneOn (fun h ↦ h * t h) (Ioi 0) := by
  intro h hh H hH hhH
  change 0 < h at hh
  change 0 < H at hH
  obtain ⟨ht, _, htS⟩ := t_spec hh
  obtain ⟨hT, _, hTS⟩ := t_spec hH
  have htT := antitoneOn_t hh hH hhH
  apply (sq_le_sq₀ (by positivity : 0 ≤ h * t h) (by positivity : 0 ≤ H * t H)).1
  have hm := mul_le_mul_of_nonneg_left htT Real.pi_pos.le
  nlinarith only [htS, hTS, hm]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def fluxArgument (h v : ℝ) : ℝ := h * v / planarProfile v

lemma div_min_positive {n a b : ℝ} (hn : 0 ≤ n) (ha : 0 < a) (hb : 0 < b) :
    n / min a b = max (n / a) (n / b) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_left (div_le_div_of_nonneg_left hn ha hab)]
  · rw [min_eq_right hba, max_eq_right (div_le_div_of_nonneg_left hn hb hba)]

lemma fluxArgument_eq {h v : ℝ} (hh : 0 ≤ h) (hv : v ∈ Ico 0 1) :
    fluxArgument h v = max (h * Real.sqrt (v / Real.pi))
      (max (h * v) (h * (v / Real.sqrt (Real.pi * (1 - v))))) := by
  rcases eq_or_lt_of_le hv.1 with hzero | hv0
  · rw [← hzero]
    simp [fluxArgument, planarProfile]
  · have hA : 0 < Real.sqrt (Real.pi * v) := Real.sqrt_pos.2 (by positivity)
    have hB : 0 < Real.sqrt (Real.pi * (1 - v)) :=
      Real.sqrt_pos.2 (mul_pos Real.pi_pos (sub_pos.2 hv.2))
    have hmin : 0 < min (1 : ℝ) (Real.sqrt (Real.pi * (1 - v))) := lt_min (by norm_num) hB
    have hn : 0 ≤ h * v := mul_nonneg hh hv.1
    unfold fluxArgument planarProfile
    rw [div_min_positive hn hA hmin, div_min_positive hn (by norm_num) hB, div_one]
    have heq : h * v / Real.sqrt (Real.pi * v) = h * Real.sqrt (v / Real.pi) := by
      rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_div hv.1]
      calc
        _ = h * (v / Real.sqrt v) / Real.sqrt Real.pi := by ring
        _ = _ := by rw [Real.div_sqrt]; ring
    rw [heq]
    congr 2
    ring

lemma fluxArgument_nonneg {h v : ℝ} (hh : 0 ≤ h) (hv : 0 ≤ v) : 0 ≤ fluxArgument h v := by
  unfold fluxArgument planarProfile
  positivity

lemma fluxArgument_continuousOn {h : ℝ} (hh : 0 ≤ h) {b : ℝ} (hb : b < 1) :
    ContinuousOn (fluxArgument h) (Icc 0 b) := by
  have hc : ContinuousOn (fun v ↦ max (h * Real.sqrt (v / Real.pi))
      (max (h * v) (h * (v / Real.sqrt (Real.pi * (1 - v)))))) (Icc 0 b) := by
    apply ContinuousOn.sup (by fun_prop)
    apply ContinuousOn.sup (by fun_prop)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_id (by fun_prop)
    intro v hv
    exact ne_of_gt (Real.sqrt_pos.2 (mul_pos Real.pi_pos (sub_pos.2 (lt_of_le_of_lt hv.2 hb))))
  apply hc.congr
  intro v hv
  exact fluxArgument_eq hh ⟨hv.1, lt_of_le_of_lt hv.2 hb⟩

lemma fluxArgument_sublevel {h X v : ℝ} (hh : 0 < h) (hX : 0 ≤ X) (hv : v ∈ Ico 0 1) :
    fluxArgument h v ≤ X ↔ v ≤ min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) := by
  have hk : 0 ≤ X / h := div_nonneg hX hh.le
  rw [fluxArgument_eq hh.le hv, max_le_iff, max_le_iff, le_min_iff, le_min_iff]
  have h1 : h * Real.sqrt (v / Real.pi) ≤ X ↔ v ≤ Real.pi * (X / h) ^ 2 := by
    rw [mul_comm h, ← le_div_iff₀ hh]
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) hk, Real.sq_sqrt (div_nonneg hv.1 Real.pi_pos.le)]
    rw [div_le_iff₀ Real.pi_pos]
    rw [mul_comm]
  have h2 : h * v ≤ X ↔ v ≤ X / h := by rw [le_div_iff₀ hh, mul_comm]
  have h3 : h * (v / Real.sqrt (Real.pi * (1 - v))) ≤ X ↔ v ≤ rho (X / h) := by
    rw [mul_comm h, ← le_div_iff₀ hh, rho_inverse_sublevel hv hk]
  exact and_congr h1 (and_congr h2 h3)

theorem fluxArgument_sublevel_set {h X : ℝ} (hh : 0 < h) (hX : X ∈ Icc 0 cutoff) :
    {v ∈ Icc 0 (t h) | fluxArgument h v ≤ X} =
      Icc 0 (min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h)))) := by
  have ht := t_spec hh
  have hX1 : X ≤ 1 := hX.2.trans cutoff_lt_one.le
  have hr : rho (X / h) ≤ t h := by
    rw [← rho_at_inverse hh]
    exact monotoneOn_rho (div_nonneg hX.1 hh.le) (show 0 ≤ (1 : ℝ) / h by positivity)
      (div_le_div_of_nonneg_right hX1 hh.le)
  have hbound : min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) ≤ t h :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans hr
  ext v
  constructor
  · rintro ⟨hv, hq⟩
    exact ⟨hv.1, (fluxArgument_sublevel hh hX.1 ⟨hv.1, hv.2.trans_lt ht.2.1⟩).1 hq⟩
  · intro hv
    have hvt : v ≤ t h := hv.2.trans hbound
    exact ⟨⟨hv.1, hvt⟩, (fluxArgument_sublevel hh hX.1 ⟨hv.1, hvt.trans_lt ht.2.1⟩).2 hv.2⟩

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def density (X : ℝ) : ℝ := X * (48 - 49 * X ^ 2) / (50 * Real.sqrt (1 - X ^ 2) ^ 3)

lemma density_nonneg {x : ℝ} (hx : x ∈ Icc 0 cutoff) : 0 ≤ density x := by
  have hs := pow_le_pow_left₀ hx.1 hx.2 2
  unfold density
  apply div_nonneg (mul_nonneg hx.1 _) (by positivity)
  nlinarith [cutoff_sq]

lemma continuousOn_density : ContinuousOn density (Icc 0 cutoff) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  have hx1 : x < 1 := hx.2.trans_lt cutoff_lt_one
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.2 hp)))

lemma hasDerivAt_neg_rawWeight {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y ↦ -rawWeight y) (density x) x := by
  convert (hasDerivAt_rawWeight hx).neg using 1
  dsimp [density]
  ring

lemma integral_density_tail {q : ℝ} (hq : q ∈ Icc 0 cutoff) :
    (∫ X in q..cutoff, density X) = rawWeight q - ell := by
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hq.2
    (continuousOn_rawWeight.neg.mono (Icc_subset_Icc_left hq.1))
    (fun x (hx : x ∈ Ioo q cutoff) ↦
      hasDerivAt_neg_rawWeight ⟨hq.1.trans_lt hx.1, hx.2.trans cutoff_lt_one⟩)
    ((continuousOn_density.mono (Icc_subset_Icc_left hq.1)).intervalIntegrable_of_Icc hq.2)
  change (∫ X in q..cutoff, density X) = -rawWeight cutoff - -rawWeight q at heq
  rw [rawWeight_cutoff] at heq
  linarith

lemma integral_density : (∫ X in (0 : ℝ)..cutoff, density X) = 18 / 25 := by
  have heq := integral_density_tail ⟨le_rfl, cutoff_pos.le⟩
  norm_num [rawWeight, ell] at heq
  exact heq

lemma weight_layer_cake {q : ℝ} (hq : 0 ≤ q) :
    weight q = ell + ∫ X in Icc 0 cutoff, if q ≤ X then density X else 0 := by
  classical
  have hrewrite : (∫ X in Icc 0 cutoff, if q ≤ X then density X else 0) =
      ∫ X in (Ici q ∩ Icc 0 cutoff), density X := by
    change (∫ X in Icc 0 cutoff, (Ici q).indicator density X) = _
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  rw [hrewrite]
  have hinter : Ici q ∩ Icc 0 cutoff = Icc q cutoff := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · tauto
    · rintro ⟨hqx, hxd⟩
      exact ⟨hqx, hq.trans hqx, hxd⟩
  rw [hinter]
  by_cases hqd : q ≤ cutoff
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hqd,
      integral_density_tail ⟨hq, hqd⟩]
    simp [weight, min_eq_left hqd]
  · have hempty : Icc q cutoff = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hqd)
    rw [hempty, setIntegral_empty, add_zero, weight, min_eq_right (le_of_not_ge hqd), rawWeight_cutoff]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma measurable_fluxArgument (h : ℝ) : Measurable (fluxArgument h) := by
  unfold fluxArgument planarProfile
  fun_prop

lemma integral_flux_sublevel {h X : ℝ} (hh : 0 < h) (hX : X ∈ Icc 0 cutoff) :
    (∫ v in Icc 0 (t h), if fluxArgument h v ≤ X then density X else 0) =
      density X * min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) := by
  classical
  let A := min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h)))
  have hA : 0 ≤ A := le_min (by positivity)
    (le_min (div_nonneg hX.1 hh.le) (rho_spec (div_nonneg hX.1 hh.le)).1)
  have hms : MeasurableSet {v | fluxArgument h v ≤ X} :=
    measurableSet_le (measurable_fluxArgument h) measurable_const
  change (∫ v in Icc 0 (t h), {v | fluxArgument h v ≤ X}.indicator (fun _ ↦ density X) v) = _
  rw [integral_indicator hms, Measure.restrict_restrict hms]
  have hs : {v | fluxArgument h v ≤ X} ∩ Icc 0 (t h) = Icc 0 A := by
    rw [inter_comm]
    exact fluxArgument_sublevel_set hh hX
  rw [hs, setIntegral_const, measureReal_def, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal hA, smul_eq_mul, mul_comm]

theorem baseline_layer_cake {h : ℝ} (hh : 0 < h) :
    baseline h + 1 = lambda * h / Real.pi + ell * t h +
      ∫ X in (0 : ℝ)..cutoff,
        density X * min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) := by
  classical
  let μ := volume.restrict (Icc 0 (t h))
  let ν := volume.restrict (Icc 0 cutoff)
  let F : ℝ × ℝ → ℝ := fun z ↦ if fluxArgument h z.1 ≤ z.2 then density z.2 else 0
  have hm : MeasurableSet {z : ℝ × ℝ | fluxArgument h z.1 ≤ z.2} :=
    measurableSet_le ((measurable_fluxArgument h).comp measurable_fst) measurable_snd
  have hF : Integrable F (μ.prod ν) := by
    exact (continuousOn_density.integrableOn_Icc.comp_snd μ).indicator hm
  have heq : (∫ v in Icc 0 (t h), weight (fluxArgument h v)) =
      ell * t h + ∫ X in Icc 0 cutoff,
        density X * min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) := by
    calc
      _ = ∫ v in Icc 0 (t h), ell + ∫ X in Icc 0 cutoff, F (v, X) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro v hv
        exact weight_layer_cake (fluxArgument_nonneg hh.le hv.1)
      _ = (∫ v in Icc 0 (t h), ell) + ∫ v in Icc 0 (t h), ∫ X in Icc 0 cutoff, F (v, X) :=
        integral_add (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
          hF.integral_prod_left
      _ = ell * t h + ∫ v in Icc 0 (t h), ∫ X in Icc 0 cutoff, F (v, X) := by
        rw [setIntegral_const, measureReal_def, Real.volume_Icc, sub_zero,
          ENNReal.toReal_ofReal (t_spec hh).1.le, smul_eq_mul, mul_comm (t h)]
      _ = ell * t h + ∫ X in Icc 0 cutoff, ∫ v in Icc 0 (t h), F (v, X) := by
        congr 1
        exact integral_integral_swap hF
      _ = _ := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro X hX
        exact integral_flux_sublevel hh hX
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (t_spec hh).1.le] at heq
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le cutoff_pos.le] at heq
  unfold baseline
  change lambda * h / Real.pi + (∫ v in (0 : ℝ)..t h, weight (fluxArgument h v)) - 1 + 1 = _
  rw [heq]
  ring

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

def rhoRoot (k : ℝ) : ℝ := Real.sqrt (Real.pi * k ^ 2 + 4)
def rhoDen (k : ℝ) : ℝ := rhoRoot k + Real.sqrt Real.pi * k
def rhoSlope (k : ℝ) : ℝ := 8 * Real.sqrt Real.pi / (rhoRoot k * rhoDen k ^ 2)

lemma rhoRoot_pos (k : ℝ) : 0 < rhoRoot k := by unfold rhoRoot; positivity
lemma rhoRoot_sq (k : ℝ) : rhoRoot k ^ 2 = Real.pi * k ^ 2 + 4 := by
  exact Real.sq_sqrt (by positivity)
lemma rhoDen_pos (k : ℝ) : 0 < rhoDen k := by
  have hs := rhoRoot_pos k
  have hs2 := rhoRoot_sq k
  have ha : (Real.sqrt Real.pi * k) ^ 2 = Real.pi * k ^ 2 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  by_contra! hn
  change rhoRoot k + Real.sqrt Real.pi * k ≤ 0 at hn
  have hk : 0 ≤ -(Real.sqrt Real.pi * k) := by linarith
  have hsq := (sq_le_sq₀ hs.le hk).2 (show rhoRoot k ≤ -(Real.sqrt Real.pi * k) by linarith)
  rw [neg_sq, ha, hs2] at hsq
  linarith

end CubicTorus.Scalar
end
end
end
end ReusedScalar205
end
end

end OAI
