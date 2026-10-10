import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

noncomputable def entropyPlus (u : ℝ) : ℝ := u * Real.log (max 1 u)

lemma entropyPlus_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ entropyPlus u := by
  exact mul_nonneg hu (Real.log_nonneg (le_max_left _ _))

lemma measurable_entropyPlus : Measurable entropyPlus := by
  unfold entropyPlus
  exact measurable_id.mul (Real.measurable_log.comp (measurable_const.max measurable_id))

lemma entropy_young {u : ℝ} (hu : 0 ≤ u) (v : ℝ) :
    u * v ≤ entropyPlus u + Real.exp v := by
  by_cases h0 : u = 0
  · simp [h0, entropyPlus, Real.exp_nonneg]
  have hp : 0 < u := lt_of_le_of_ne hu (Ne.symm h0)
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v - Real.log u)) hu
  have heq : u * Real.exp (v - Real.log u) = Real.exp v := by
    rw [Real.exp_sub, Real.exp_log hp]
    field_simp
  rw [heq] at he
  have hlog : Real.log u ≤ Real.log (max 1 u) :=
    Real.log_le_log hp (le_max_right _ _)
  have hm := mul_le_mul_of_nonneg_left hlog hu
  unfold entropyPlus
  nlinarith

section Integrability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integrable_density_mul_of_entropy {f z : Ω → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : Measurable f) (hz : Measurable z)
    (hf0 : ∀ x, 0 ≤ f x) (hz0 : ∀ x, 0 ≤ z x)
    (hH : Integrable (fun x => entropyPlus (f x)) μ)
    (he : Integrable (fun x => Real.exp (c * z x)) μ) :
    Integrable (fun x => f x * z x) μ := by
  apply ((hH.add he).div_const c).mono' (hf.mul hz).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖f x * z x‖ ≤ (entropyPlus (f x) + Real.exp (c * z x)) / c
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (hz0 x))]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using entropy_young (hf0 x) (c * z x)

lemma exp_on_density_tail_pointwise {u z c L B : ℝ}
    (hu : 0 ≤ u) (hc : 0 ≤ c) (hB : 0 < B) :
    (if B < u then Real.exp (c * z) else 0) ≤
      (Real.exp (c * L) / B) * u +
        Real.exp (-c * L) * Real.exp ((2 * c) * z) := by
  by_cases ht : B < u
  · rw [ite_eq_left ht]
    by_cases hz : z ≤ L
    · apply le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hc))
      have hb : 1 ≤ u / B := (le_div_iff₀ hB).mpr (by linarith)
      have he := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (c * L))
      have hp : 0 ≤ Real.exp (-c * L) * Real.exp ((2 * c) * z) := by positivity
      have heq : Real.exp (c * L) * (u / B) = Real.exp (c * L) / B * u := by ring
      rw [mul_one, heq] at he
      exact he.trans (le_add_of_nonneg_right hp)
    · have hzl : L ≤ z := le_of_not_ge hz
      have hle : c * z ≤ -c * L + (2 * c) * z := by
        nlinarith [mul_nonneg hc (sub_nonneg.mpr hzl)]
      calc
        Real.exp (c * z) ≤ Real.exp (-c * L + (2 * c) * z) := Real.exp_le_exp.mpr hle
        _ = Real.exp (-c * L) * Real.exp ((2 * c) * z) := Real.exp_add _ _
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
  · rw [ite_eq_right ht]
    positivity

lemma density_tail_pointwise {u z c L B : ℝ}
    (hu : 0 ≤ u) (hz : 0 ≤ z) (hc : 0 < c) (hB : 0 < B) :
    c * (if B < u then u * z else 0) ≤
      (if B < u then entropyPlus u else 0) +
        (Real.exp (c * L) / B) * u +
          Real.exp (-c * L) * Real.exp ((2 * c) * z) := by
  rcases hz.eq_or_lt with rfl | _
  · have hEntropy := entropyPlus_nonneg hu
    simp only [mul_zero, ite_self]
    split_ifs <;> positivity
  · have he := exp_on_density_tail_pointwise (u := u) (z := z) (L := L) hu hc.le hB
    by_cases h : B < u
    · simp only [ite_eq_left h] at *
      have hy := entropy_young hu (c * z)
      nlinarith
    · simp only [ite_eq_right h, mul_zero, zero_add]
      positivity

lemma integrable_entropy_tail {f : Ω → ℝ} (hf : Measurable f)
    (hH : Integrable (fun x => entropyPlus (f x)) μ) (B : ℝ) :
    Integrable (fun x => if B < f x then entropyPlus (f x) else 0) μ := by
  apply hH.norm.mono'
    ((measurable_entropyPlus.comp hf).ite (measurableSet_lt measurable_const hf) measurable_const).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖if B < f x then entropyPlus (f x) else 0‖ ≤ ‖entropyPlus (f x)‖
  split_ifs <;> simp only [le_refl, norm_zero, norm_nonneg]

lemma entropy_tail_tendsto {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hH : Integrable (fun x => entropyPlus (f x)) μ) :
    Tendsto (fun n : ℕ => ∫ x, if (n : ℝ) < f x then entropyPlus (f x) else 0 ∂μ)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => if (n : ℝ) < f x then entropyPlus (f x) else 0) μ :=
    (integrable_entropy_tail hf hH n).aestronglyMeasurable
  have hb (n : ℕ) (x : Ω) :
      ‖(if (n : ℝ) < f x then entropyPlus (f x) else 0)‖ ≤ entropyPlus (f x) := by
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (entropyPlus_nonneg (hf0 x))]
    · simpa only [norm_zero] using entropyPlus_nonneg (hf0 x)
  have ht : ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => if (n : ℝ) < f x then entropyPlus (f x) else 0) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge (f x)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : f x ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
    simp only [not_lt.mpr hn', ite_false]
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun x => entropyPlus (f x)) hm hH
    (fun n => Eventually.of_forall (hb n)) ht

lemma density_tail_integral_le {f z : Ω → ℝ} {c B L : ℝ}
    (hc : 0 < c) (hB : 0 < B) (hf : Measurable f) (hz : Measurable z)
    (hf0 : ∀ x, 0 ≤ f x) (hz0 : ∀ x, 0 ≤ z x)
    (hfi : Integrable f μ) (hH : Integrable (fun x => entropyPlus (f x)) μ)
    (he : Integrable (fun x => Real.exp ((2 * c) * z x)) μ) :
    (∫ x, if B < f x then f x * z x else 0 ∂μ) ≤
      ((∫ x, if B < f x then entropyPlus (f x) else 0 ∂μ) +
        (Real.exp (c * L) / B) * (∫ x, f x ∂μ) +
          Real.exp (-c * L) * (∫ x, Real.exp ((2 * c) * z x) ∂μ)) / c := by
  have hei : Integrable (fun x => Real.exp (c * z x)) μ := by
    apply he.mono' (Real.measurable_exp.comp (measurable_const.mul hz)).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖Real.exp (c * z x)‖ ≤ Real.exp ((2 * c) * z x)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith [hz0 x])
  have hprod := integrable_density_mul_of_entropy hc hf hz hf0 hz0 hH hei
  have htail : Integrable (fun x => if B < f x then f x * z x else 0) μ := by
    apply hprod.norm.mono'
      ((hf.mul hz).ite (measurableSet_lt measurable_const hf) measurable_const).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖if B < f x then f x * z x else 0‖ ≤ ‖f x * z x‖
    split_ifs <;> simp only [le_refl, norm_zero, norm_nonneg]
  have hEt := integrable_entropy_tail hf hH B
  have hsum : Integrable (fun x => (if B < f x then entropyPlus (f x) else 0) +
      (Real.exp (c * L) / B) * f x) μ := hEt.add (hfi.const_mul _)
  have hi := integral_mono (htail.const_mul c)
    (hsum.add (he.const_mul (Real.exp (-c * L))))
    (fun x => density_tail_pointwise (L := L) (hf0 x) (hz0 x) hc hB)
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,
    integral_add hsum (he.const_mul _),
    integral_add hEt (hfi.const_mul _), integral_const_mul, integral_const_mul] at hi
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using hi

lemma remainder_cap_pointwise {z c K : ℝ} (hz : 0 ≤ z) (hc : 0 < c) :
    z - min K z ≤ (Real.exp (-c * K) / c) * Real.exp ((2 * c) * z) := by
  by_cases h : z ≤ K
  · rw [min_eq_right h, sub_self]
    positivity
  · have hK : K ≤ z := le_of_not_ge h
    rw [min_eq_left hK]
    have h0 : c * (z - K) ≤ Real.exp (c * (z - K)) := by
      linarith [Real.add_one_le_exp (c * (z - K))]
    have h1 : c * (z - K) ≤ -c * K + (2 * c) * z := by nlinarith
    have h2 := Real.exp_le_exp.mpr h1
    rw [Real.exp_add] at h2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using h0.trans h2

lemma exp_neg_nat_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c * (n : ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp ht using 1
  funext n
  simp only [Function.comp_apply, neg_mul]

lemma uniform_density_tail {f : Ω → ℝ} {Z : ℕ → Ω → ℝ} {c Q : ℝ}
    (hc : 0 < c) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f μ) (hH : Integrable (fun x => entropyPlus (f x)) μ)
    (hZ : ∀ r, Measurable (Z r)) (hZ0 : ∀ r x, 0 ≤ Z r x)
    (he : ∀ r, Integrable (fun x => Real.exp ((2 * c) * Z r x)) μ)
    (heQ : ∀ r, (∫ x, Real.exp ((2 * c) * Z r x) ∂μ) ≤ Q) :
    ∀ ε > 0, ∃ B > 1, ∀ r,
      (∫ x, if B < f x then f x * Z r x else 0 ∂μ) < ε := by
  let F := ∫ x, f x ∂μ
  have hF : 0 ≤ F := integral_nonneg hf0
  have ht : Tendsto (fun n : ℕ =>
      ((∫ x, if (n : ℝ) < f x then entropyPlus (f x) else 0 ∂μ) +
        Real.exp (-c * (n : ℝ)) * (F + Q)) / c) atTop (𝓝 0) := by
    simpa only [zero_mul, zero_add, zero_div] using
      ((entropy_tail_tendsto hf hf0 hH).add ((exp_neg_nat_tendsto hc).mul_const (F + Q))).div_const c
  intro ε hε
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const hε).exists
  let L : ℝ := n
  let B : ℝ := Real.exp ((2 * c) * L) + L + 1
  have hL : 0 ≤ L := Nat.cast_nonneg n
  have hB : 1 < B := by dsimp [B]; linarith [Real.exp_pos ((2 * c) * L)]
  have hBn : (n : ℝ) ≤ B := by dsimp [B, L]; linarith [Real.exp_pos ((2 * c) * (n : ℝ))]
  have hcoeff : Real.exp (c * L) / B ≤ Real.exp (-c * L) := by
    apply (div_le_iff₀ (lt_trans zero_lt_one hB)).mpr
    have hscale : Real.exp (-c * L) * Real.exp ((2 * c) * L) = Real.exp (c * L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (c * L) = Real.exp (-c * L) * Real.exp ((2 * c) * L) := hscale.symm
      _ ≤ Real.exp (-c * L) * B := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        dsimp [B]
        linarith
  have hHtail : (∫ x, if B < f x then entropyPlus (f x) else 0 ∂μ) ≤
      ∫ x, if (n : ℝ) < f x then entropyPlus (f x) else 0 ∂μ := by
    apply integral_mono (integrable_entropy_tail hf hH B) (integrable_entropy_tail hf hH n)
    intro x
    change (if B < f x then entropyPlus (f x) else 0) ≤
      (if (n : ℝ) < f x then entropyPlus (f x) else 0)
    by_cases h : B < f x
    · rw [ite_eq_left h, ite_eq_left (lt_of_le_of_lt hBn h)]
    · rw [ite_eq_right h]
      split_ifs
      · exact entropyPlus_nonneg (hf0 x)
      · exact le_rfl
  refine ⟨B, hB, ?_⟩
  intro r
  apply lt_of_le_of_lt (density_tail_integral_le (c := c) (B := B) (L := L)
    hc (lt_trans zero_lt_one hB) hf (hZ r) hf0 (hZ0 r) hfi hH (he r))
  apply lt_of_le_of_lt _ hn
  apply div_le_div_of_nonneg_right _ hc.le
  have h1 := mul_le_mul_of_nonneg_right hcoeff hF
  have h2 := mul_le_mul_of_nonneg_left (heQ r) (Real.exp_nonneg (-c * L))
  dsimp [F, L] at *
  nlinarith

lemma cap_error_integrable {f z : Ω → ℝ} {c B K : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hf : Measurable f) (hz : Measurable z)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) (hz0 : ∀ x, 0 ≤ z x)
    (he : Integrable (fun x => Real.exp ((2 * c) * z x)) μ) :
    Integrable (fun x => f x * (z x - min K (z x))) μ := by
  apply (he.const_mul (B * (Real.exp (-c * K) / c))).mono'
    (hf.mul (hz.sub (measurable_const.min hz))).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖f x * (z x - min K (z x))‖ ≤ B * (Real.exp (-c * K) / c) * Real.exp ((2 * c) * z x)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (sub_nonneg.mpr (min_le_right _ _)))]
  have hbound := mul_le_mul (hfB x) (remainder_cap_pointwise (K := K) (hz0 x) hc)
    (sub_nonneg.mpr (min_le_right K (z x))) hB
  simpa only [mul_assoc] using hbound

lemma cap_error_integral_le {f z : Ω → ℝ} {c B K : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hf : Measurable f) (hz : Measurable z)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) (hz0 : ∀ x, 0 ≤ z x)
    (he : Integrable (fun x => Real.exp ((2 * c) * z x)) μ) :
    (∫ x, f x * (z x - min K (z x)) ∂μ) ≤
      (B * (Real.exp (-c * K) / c)) * (∫ x, Real.exp ((2 * c) * z x) ∂μ) := by
  rw [← integral_const_mul]
  apply integral_mono (cap_error_integrable hc hB hf hz hf0 hfB hz0 he) (he.const_mul _)
  intro x
  have hbound := mul_le_mul (hfB x) (remainder_cap_pointwise (K := K) (hz0 x) hc)
    (sub_nonneg.mpr (min_le_right K (z x))) hB
  simpa only [mul_assoc] using hbound

lemma uniform_remainder_cap {f : Ω → ℝ} {Z : ℕ → Ω → ℝ} {c B Q : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hZ : ∀ r, Measurable (Z r)) (hZ0 : ∀ r x, 0 ≤ Z r x)
    (he : ∀ r, Integrable (fun x => Real.exp ((2 * c) * Z r x)) μ)
    (heQ : ∀ r, (∫ x, Real.exp ((2 * c) * Z r x) ∂μ) ≤ Q) :
    ∀ ε > 0, ∃ K > 0, ∀ r,
      (∫ x, f x * (Z r x - min K (Z r x)) ∂μ) < ε := by
  have ht : Tendsto (fun n : ℕ => B * (Real.exp (-c * (n : ℝ)) / c) * Q)
      atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero, zero_mul] using
      (((exp_neg_nat_tendsto hc).div_const c).const_mul B).mul_const Q
  intro ε hε
  obtain ⟨n, hn0, hn⟩ := ((eventually_gt_atTop 0).and (ht.eventually_lt_const hε)).exists
  refine ⟨n, by exact_mod_cast hn0, ?_⟩
  intro r
  apply lt_of_le_of_lt (cap_error_integral_le (K := n) hc hB hf (hZ r) hf0 hfB (hZ0 r) (he r))
  apply lt_of_le_of_lt _ hn
  exact mul_le_mul_of_nonneg_left (heQ r) (by positivity)

end Integrability

end TailDecorrelation

end

end OAI
