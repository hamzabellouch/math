import Mathlib
import OAI.Probability.SLELocalization.TraceModel
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Localization estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

lemma physical_clock_bounds {T δ Y₀ u : ℝ} {Y C Q : ℝ → ℝ}
    (hT : 0 ≤ T) (hδ : 0 < δ) (hY₀ : 0 < Y₀) (hYinit : Y 0 = Y₀) (hCinit : C 0 = 0)
    (hY : ContinuousOn Y (Icc 0 T)) (hC : ContinuousOn C (Icc 0 T))
    (hYpos : ∀ t ∈ Icc 0 T, 0 < Y t)
    (hYle : ∀ t ∈ Icc 0 T, Y t ≤ Y₀)
    (hQpos : ∀ t ∈ Ioo 0 T, 0 < Q t)
    (hangle : ∀ t ∈ Ioo 0 T, δ^2 * Q t ≤ (Y t)^2)
    (hdY : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => Real.log (Y s)) (-2 / Q t) t)
    (hdC : ∀ t ∈ Ioo 0 T, HasDerivAt C (4*(Y t)^2 / (Q t)^2) t)
    (hCu : C T ≤ u) :
    Y₀ * Real.exp (-u/(2*δ^2)) ≤ Y T ∧ T ≤ u * Y₀^2 / (4*δ^4) := by
  have hd2 : 0 < δ^2 := sq_pos_of_pos hδ
  have hq2 (t : ℝ) (ht : t ∈ Ioo 0 T) : 0 < Q t ^ 2 := sq_pos_of_pos (hQpos t ht)
  have hlogY := hY.log (fun t ht => (hYpos t ht).ne')
  have hm : MonotoneOn (fun t => Real.log (Y t) + C t / (2*δ^2)) (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (hlogY.add (hC.div_const _))
      (f' := fun t => -2/Q t + (4*(Y t)^2/(Q t)^2)/(2*δ^2))
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hdY t ht).add ((hdC t ht).div_const _)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hq := hQpos t ht
      have ha := hangle t ht
      apply (mul_le_mul_iff_of_pos_right (mul_pos (hq2 t ht) (mul_pos (by norm_num : (0:ℝ)<2) hd2))).1
      field_simp
      nlinarith
  have hlogbound := hm ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT
  simp only [hYinit, hCinit, zero_div, add_zero] at hlogbound
  have hL : Real.log Y₀ + (-u/(2*δ^2)) ≤ Real.log (Y T) := by
    have hh : C T/(2*δ^2) ≤ u/(2*δ^2) :=
      div_le_div_of_nonneg_right hCu (mul_pos (by norm_num) hd2).le
    simp only [neg_div]
    linarith
  have hheight : Y₀ * Real.exp (-u/(2*δ^2)) ≤ Y T := by
    have hh := Real.exp_le_exp.mpr hL
    simpa only [Real.exp_add, Real.exp_log hY₀, Real.exp_log (hYpos T ⟨hT,le_rfl⟩)] using hh
  have hK : 0 < 4*δ^4/Y₀^2 := by positivity
  have hderivbound (t : ℝ) (ht : t ∈ Ioo 0 T) :
      4*δ^4/Y₀^2 ≤ 4*(Y t)^2/(Q t)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hY₀) (hq2 t ht)).2
    have ha := hangle t ht
    have hb : (δ^2*Q t)^2 ≤ ((Y t)^2)^2 :=
      pow_le_pow_left₀ (mul_nonneg hd2.le (hQpos t ht).le) ha 2
    have hc : (Y t)^2 ≤ Y₀^2 :=
      pow_le_pow_left₀ (hYpos t ⟨ht.1.le,ht.2.le⟩).le (hYle t ⟨ht.1.le,ht.2.le⟩) 2
    have he := mul_le_mul_of_nonneg_left hc (sq_nonneg (Y t))
    nlinarith
  have hmC : MonotoneOn (fun t => C t - (4*δ^4/Y₀^2)*t) (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (hC.sub (continuousOn_id.const_mul _))
      (f' := fun t => 4*(Y t)^2/(Q t)^2 - (4*δ^4/Y₀^2))
    · intro t ht
      rw [interior_Icc] at ht
      simpa only [mul_one] using
        ((hdC t ht).sub ((hasDerivAt_id t).const_mul (4*δ^4/Y₀^2))).hasDerivWithinAt
          (s := interior (Icc 0 T))
    · intro t ht
      rw [interior_Icc] at ht
      exact sub_nonneg.2 (hderivbound t ht)
  have htime := hmC ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT
  simp only [hCinit, mul_zero, sub_zero] at htime
  refine ⟨hheight, ?_⟩
  have hh : T ≤ u / (4*δ^4/Y₀^2) := (le_div_iff₀ hK).2 (by linarith)
  convert hh using 1
  field_simp

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.IsLoewnerTraceUsing
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma finite_clock_bounds (h : IsLoewnerTraceUsing driver γ g f)
    {T δ u : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hU : ContinuousOn driver (Icc 0 T)) {z : ℂ} (hz : z ∈ localizationDomain γ T)
    (hangle : ∀ t ∈ Ioo 0 T,
      δ^2 * Complex.normSq (g t z - (driver t : ℂ)) ≤ (g t z).im^2)
    (hr : (2*z.im)*Real.exp (-u) ≤ loewnerRadius g T z) :
    z.im * Real.exp (-u/(2*δ^2)) ≤ (g T z).im ∧
      T ≤ u*z.im^2/(4*δ^4) := by
  have hz0 : z ∈ halfPlane := hz.1.1
  have hy0 : 0 < z.im := hz0
  let C : ℝ → ℝ := fun t => Real.log (2*z.im) - Real.log (loewnerRadius g t z)
  apply physical_clock_bounds (Y := fun t => (g t z).im) (C := C)
    (Q := fun t => Complex.normSq (g t z - (driver t : ℂ))) hT hδ hy0
  · rw [h.initial z hz0]
  · simp only [C, h.radius_initial hz0, sub_self]
  · exact Complex.continuous_im.comp_continuousOn (h.continuous_eval hT hz)
  · exact continuousOn_const.sub (h.continuous_log_radius hT hU hz)
  · intro t ht
    exact h.im_pos ht.1 (survivingDomain_mono ht.2 hz)
  · intro t ht
    exact h.height_le_initial ht.1 (survivingDomain_mono ht.2 hz)
  · intro t ht
    exact Complex.normSq_pos.2 (h.centered_ne_zero ht.1.le (survivingDomain_mono ht.2.le hz))
  · exact hangle
  · intro t ht
    have hi := h.im_pos ht.1.le (survivingDomain_mono ht.2.le hz)
    apply ((h.hasDerivAt_height ht.1 (survivingDomain_mono ht.2.le hz)).log hi.ne').congr_deriv
    field_simp
  · intro t ht
    change HasDerivAt (fun s => Real.log (2*z.im) - Real.log (loewnerRadius g s z)) _ t
    apply ((h.hasDerivAt_log_radius hT hU hz ht).const_sub (Real.log (2*z.im))).congr_deriv
    ring
  · have hh := Real.log_le_log (mul_pos (mul_pos (by norm_num) hy0) (Real.exp_pos (-u))) hr
    rw [Real.log_mul (mul_ne_zero (by norm_num) hy0.ne') (Real.exp_ne_zero _), Real.log_exp] at hh
    dsimp [C]
    linarith

end SLEExactGauge.IsLoewnerTraceUsing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.PartitionMeshes
open TaylorMeshes TimeField

structure PartitionSequence (T : ℝ) where
  count : ℕ → ℕ
  time : ℕ → ℕ → ℝ
  step : ℕ → ℝ
  start : ∀ n, time n 0 = 0
  finish : ∀ n, time n (count n) = T
  mono : ∀ n, Monotone (time n)
  step_le : ∀ n i, i < count n → time n (i+1)-time n i ≤ step n
  step_zero : Tendsto step atTop (𝓝 0)

end SLEExactGauge.PartitionMeshes

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.PartitionMeshes
open TaylorMeshes TimeField
namespace PartitionSequence
variable {T : ℝ} (p : PartitionSequence T)

include p in
lemma nonneg : 0 ≤ T := by
  simpa only [p.start, p.finish] using p.mono 0 (Nat.zero_le (p.count 0))

lemma mem (n i : ℕ) (hi : i ≤ p.count n) : p.time n i ∈ Icc 0 T := by
  constructor
  · simpa only [p.start] using p.mono n (Nat.zero_le i)
  · simpa only [p.finish] using p.mono n hi

lemma increments_small {b : ℝ → ℝ} (hb : ContinuousOn b (Icc 0 T))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ i < p.count n, |b (p.time n (i+1))-b (p.time n i)| < δ := by
  obtain ⟨ε, hε, hmod⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hb) δ hδ
  filter_upwards [p.step_zero.eventually (gt_mem_nhds hε)] with n hn
  intro i hi
  apply hmod _ (p.mem n (i+1) hi) _ (p.mem n i hi.le)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (p.mono n (Nat.le_succ i)))]
  exact (p.step_le n i hi).trans_lt hn

lemma riemann_tendsto {h : ℝ → ℝ} (hh : ContinuousOn h (Icc 0 T)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      h (p.time n i) * (p.time n (i+1)-p.time n i)) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, h t)) := by
  have hT := p.nonneg
  have hint (n i : ℕ) (hi : i < p.count n) :
      IntervalIntegrable h volume (p.time n i) (p.time n (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (p.mono n (Nat.le_succ i))]
    exact hh.mono (Icc_subset_Icc (p.mem n i hi.le).1 (p.mem n (i+1) hi).2)
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hh
  apply Metric.tendsto_atTop.2
  intro ε hε
  let ζ : ℝ := ε / (T+1)
  have hζ : 0 < ζ := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 hu ζ hζ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (p.step_zero.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  have hnδ := hN n hn
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (fun i hi => hint n i hi)
  rw [p.start, p.finish] at hsum
  have heach (i : ℕ) (hi : i < p.count n) :
      |h (p.time n i) * (p.time n (i+1)-p.time n i) -
        ∫ t in p.time n i..p.time n (i+1), h t| ≤
          ζ * (p.time n (i+1)-p.time n i) := by
    have heq : h (p.time n i) * (p.time n (i+1)-p.time n i) =
        ∫ _ : ℝ in p.time n i..p.time n (i+1), h (p.time n i) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [heq, ← intervalIntegral.integral_sub intervalIntegrable_const (hint n i hi)]
    have hbound : ∀ t ∈ uIoc (p.time n i) (p.time n (i+1)),
        ‖h (p.time n i)-h t‖ ≤ ζ := by
      intro t ht
      rw [uIoc_of_le (p.mono n (Nat.le_succ i))] at ht
      have htT : t ∈ Icc 0 T := ⟨(p.mem n i hi.le).1.trans ht.1.le,
        ht.2.trans (p.mem n (i+1) hi).2⟩
      have hd : dist (p.time n i) t < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 ht.1.le)]
        have hs := p.step_le n i hi
        have ht' := ht.2
        linarith
      simpa only [Real.norm_eq_abs, Real.dist_eq] using
        (hmod _ (p.mem n i hi.le) _ htT hd).le
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.2 (p.mono n (Nat.le_succ i)))] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.dist_eq, ← hsum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range (p.count n),
        |h (p.time n i) * (p.time n (i+1)-p.time n i) -
          ∫ t in p.time n i..p.time n (i+1), h t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (p.count n), ζ * (p.time n (i+1)-p.time n i) :=
      Finset.sum_le_sum (fun i hi => heach i (Finset.mem_range.1 hi))
    _ = ζ * T := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (p.time n), p.start, p.finish, sub_zero]
    _ < ε := by
      dsimp only [ζ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < T+1)]
      nlinarith

lemma family_remainder_tendsto {f : ℕ → ℕ → ℝ → ℝ} {b : ℝ → ℝ}
    (hf : ∀ n i, ContDiff ℝ 3 (f n i))
    {V K : ℝ} (hb : ContinuousOn b (Icc 0 T)) (hK : 0 ≤ K)
    (h3 : ∀ n i x, |iteratedDeriv 3 (f n i) x| ≤ K)
    (hQ : Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      (b (p.time n (i+1))-b (p.time n i))^2) atTop (𝓝 V)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      remainder₂ (f n i) (b (p.time n i)) (b (p.time n (i+1)))) atTop (𝓝 0) := by
  have hV : 0 ≤ V := ge_of_tendsto hQ
    (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε / ((K+1)*(V+1))
  have hδ : 0 < δ := div_pos hε (mul_pos (by linarith) (by linarith))
  have hs := p.increments_small hb hδ
  have hq := hQ.eventually (gt_mem_nhds (show V < V+1 by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.and hq)
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨hs, hq⟩
  have hr := sum_family_remainder₂_bound (hf n) (fun i => b (p.time n i))
    (p.count n) K δ hK hδ.le (fun i _ z _ => h3 n i z) (fun i hi => (hs i hi).le)
  simp only [Real.dist_eq, sub_zero]
  calc
    _ ≤ K * δ / 6 * ∑ i ∈ Finset.range (p.count n),
        (b (p.time n (i+1))-b (p.time n i))^2 := hr
    _ ≤ K * δ / 6 * (V+1) := mul_le_mul_of_nonneg_left hq.le (by positivity)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < (K+1)*(V+1) := mul_pos (by linarith) (by linarith)
      have hid : K * (ε / ((K+1)*(V+1))) / 6 * (V+1) = ε * (K / (6*(K+1))) := by
        field_simp
      rw [hid]
      have hk : K / (6*(K+1)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      simpa using mul_lt_mul_of_pos_left hk hε

end PartitionSequence

end SLEExactGauge.PartitionMeshes

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.PartitionMeshes
open TaylorMeshes TimeField

def clippedDyadic (T τ : ℝ) (hT : 0 ≤ T) (hτ : 0 ≤ τ) (hτT : τ ≤ T) :
    PartitionSequence τ where
  count := fun n => 2^n
  time := fun n i => min (mesh T n i) τ
  step := fun n => T / (2 : ℝ)^n
  start := fun n => by rw [mesh_zero, min_eq_left hτ]
  finish := fun n => by rw [mesh_end, min_eq_right hτT]
  mono := fun n i j hij => min_le_min_right τ (mesh_mono T hT n hij)
  step_le := by
    intro n i hi
    have hm := mesh_mono T hT n (Nat.le_succ i)
    have hs := mesh_step T n i
    by_cases h₁ : mesh T n i ≤ τ
    · rw [min_eq_left h₁]
      have hb := min_le_left (mesh T n (i+1)) τ
      linarith
    · rw [min_eq_right (le_of_not_ge h₁),
        min_eq_right ((le_of_not_ge h₁).trans hm)]
      simp only [sub_self]
      positivity
  step_zero := mesh_step_tendsto T

end SLEExactGauge.PartitionMeshes

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.PartitionMeshes.PartitionSequence
open SLEExactGauge.TaylorMeshes SLEExactGauge.TimeField

lemma time_increment_tendsto {T : ℝ} (p : PartitionSequence T)
    {F V : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hF : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T))
    (hD : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun u => F u x) (V t x) t)
    (hV : ContinuousOn (fun q : ℝ × ℝ => V q.1 (b q.2)) ((Icc 0 T) ×ˢ (Icc 0 T))) :
    Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      (F (p.time n (i+1)) (b (p.time n (i+1))) -
        F (p.time n i) (b (p.time n (i+1))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, V t (b t))) := by
  have hT := p.nonneg
  have hVc : ContinuousOn (fun t => V t (b t)) (Icc 0 T) :=
    hV.comp (continuousOn_id.prodMk continuousOn_id) (fun t ht => ⟨ht, ht⟩)
  have hriem := p.riemann_tendsto hVc
  have herror : Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      (F (p.time n (i+1)) (b (p.time n (i+1))) -
        F (p.time n i) (b (p.time n (i+1))) -
          V (p.time n i) (b (p.time n i)) * (p.time n (i+1)-p.time n i)))
          atTop (𝓝 0) := by
    have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hV
    apply Metric.tendsto_atTop.2
    intro ε hε
    let ζ : ℝ := ε / (T+1)
    have hζ : 0 < ζ := div_pos hε (by linarith)
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 hu ζ hζ
    obtain ⟨N, hN⟩ := eventually_atTop.1 (p.step_zero.eventually (gt_mem_nhds hδ))
    refine ⟨N, fun n hn => ?_⟩
    have hnδ := hN n hn
    have heach (i : ℕ) (hi : i < p.count n) :
        |F (p.time n (i+1)) (b (p.time n (i+1))) -
          F (p.time n i) (b (p.time n (i+1))) -
            V (p.time n i) (b (p.time n i)) * (p.time n (i+1)-p.time n i)| ≤
        ζ * (p.time n (i+1)-p.time n i) := by
      rcases (p.mono n (Nat.le_succ i)).eq_or_lt with heq | hstep_pos
      · simp [heq]
      have hleft := p.mem n i hi.le
      have hright := p.mem n (i+1) hi
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
        (fun t => F t (b (p.time n (i+1)))) (fun t => V t (b (p.time n (i+1))))
        hstep_pos ((hF _).mono (Icc_subset_Icc hleft.1 hright.2))
        (fun t ht => hD t ⟨hleft.1.trans_lt ht.1, ht.2.trans_le hright.2⟩ _)
      have hcT : c ∈ Icc 0 T := ⟨hleft.1.trans hc.1.le, hc.2.le.trans hright.2⟩
      have hdist : dist (c, p.time n (i+1)) (p.time n i, p.time n i) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        constructor
        · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hc.1.le)]
          have hcs := hc.2
          have hstep := p.step_le n i hi
          linarith
        · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hstep_pos.le)]
          exact (p.step_le n i hi).trans_lt hnδ
      have hvmod := (hmod (c, p.time n (i+1)) ⟨hcT, hright⟩
        (p.time n i, p.time n i) ⟨hleft, hleft⟩ hdist).le
      simp only [Real.dist_eq] at hvmod
      have hid : F (p.time n (i+1)) (b (p.time n (i+1))) -
          F (p.time n i) (b (p.time n (i+1))) =
          V c (b (p.time n (i+1))) * (p.time n (i+1)-p.time n i) :=
        ((eq_div_iff (sub_pos.2 hstep_pos).ne').1 heq).symm
      rw [hid, ← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 hstep_pos.le)]
      exact mul_le_mul_of_nonneg_right hvmod (sub_nonneg.2 hstep_pos.le)
    rw [Real.dist_eq, sub_zero]
    calc
      _ ≤ ∑ i ∈ Finset.range (p.count n),
          |F (p.time n (i+1)) (b (p.time n (i+1))) -
            F (p.time n i) (b (p.time n (i+1))) -
              V (p.time n i) (b (p.time n i)) * (p.time n (i+1)-p.time n i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (p.count n), ζ * (p.time n (i+1)-p.time n i) :=
        Finset.sum_le_sum (fun i hi => heach i (Finset.mem_range.1 hi))
      _ = ζ * T := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (p.time n), p.start, p.finish, sub_zero]
      _ < ε := by
        dsimp [ζ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < T+1)]
        nlinarith
  have hadd := herror.add hriem
  simp only [Finset.sum_sub_distrib, sub_add_cancel, zero_add] at hadd
  simpa only [Finset.sum_sub_distrib] using hadd

end SLEExactGauge.PartitionMeshes.PartitionSequence

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.StoppedMeshes
open TaylorMeshes PartitionMeshes

lemma one_crossing_sum_bound {N : ℕ} {t : ℕ → ℝ} (ht : Monotone t)
    {τ E : ℝ} (hE : 0 ≤ E) {f : ℕ → ℝ}
    (hz : ∀ i < N, ¬ (t i < τ ∧ τ < t (i+1)) → f i = 0)
    (hb : ∀ i < N, t i < τ ∧ τ < t (i+1) → |f i| ≤ E) :
    |∑ i ∈ Finset.range N, f i| ≤ E := by
  classical
  by_cases he : ∃ i < N, t i < τ ∧ τ < t (i+1)
  · obtain ⟨i, hi, hcross⟩ := he
    rw [Finset.sum_eq_single i]
    · exact hb i hi hcross
    · intro j hj hji
      apply hz j (Finset.mem_range.1 hj)
      intro hcj
      rcases lt_or_gt_of_ne hji with hji | hij
      · have hm := ht (show j+1 ≤ i by omega)
        linarith [hcj.2, hcross.1]
      · have hm := ht (show i+1 ≤ j by omega)
        linarith [hcross.2, hcj.1]
    · intro hni
      exact (hni (Finset.mem_range.2 hi)).elim
  · have heq : ∑ i ∈ Finset.range N, f i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply hz i (Finset.mem_range.1 hi)
      intro hc
      exact he ⟨i, Finset.mem_range.1 hi, hc⟩
    simpa [heq] using hE

lemma clipped_increment_eq {a c τ : ℝ} (hac : a ≤ c) (b : ℝ → ℝ)
    (hn : ¬ (a < τ ∧ τ < c)) :
    b (min c τ) - b (min a τ) = if a < τ then b c - b a else 0 := by
  by_cases ha : a < τ
  · rw [ite_eq_left ha, min_eq_left ha.le, min_eq_left (le_of_not_gt (fun hc => hn ⟨ha,hc⟩))]
  · have hτa : τ ≤ a := le_of_not_gt ha
    rw [ite_eq_right ha, min_eq_right hτa, min_eq_right (hτa.trans hac), sub_self]

lemma clipped_timeSum_difference_tendsto {T τ : ℝ} (hT : 0 ≤ T)
    (A : ℕ → ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K) (hA : ∀ n i, |A n i| ≤ K) :
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (2^n), A n i *
        (min (mesh T n (i+1)) τ - min (mesh T n i) τ)) -
      (∑ i ∈ Finset.range (2^n),
        if mesh T n i < τ then A n i * (T / (2 : ℝ)^n) else 0)) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun n => K * (T / (2 : ℝ)^n)) (fun n => ?_) ?_
  · rw [Real.norm_eq_abs, ← Finset.sum_sub_distrib]
    apply one_crossing_sum_bound (τ := τ) (mesh_mono T hT n) (mul_nonneg hK (by positivity))
    · intro i hi hn
      have heq := clipped_increment_eq (mesh_mono T hT n (Nat.le_succ i)) id hn
      dsimp only [id_eq] at heq
      rw [heq]
      split_ifs <;> simp [mesh_step]
    · intro i hi hc
      rw [min_eq_right hc.2.le, min_eq_left hc.1.le, ite_eq_left hc.1]
      rw [← mul_sub, abs_mul]
      apply le_trans (mul_le_mul_of_nonneg_right (hA n i) (abs_nonneg _))
      apply mul_le_mul_of_nonneg_left _ hK
      have hs := mesh_step T n i
      rw [abs_of_nonpos (by linarith)]
      linarith [hc.1]
  · simpa using (mesh_step_tendsto T).const_mul K

lemma clipped_linearSum_difference_tendsto {T τ : ℝ} (hT : 0 ≤ T)
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) {b : ℝ → ℝ}
    (hb : ContinuousOn b (Icc 0 T)) (A : ℕ → ℕ → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ n i, |A n i| ≤ K) :
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (2^n), A n i *
        (b (min (mesh T n (i+1)) τ) - b (min (mesh T n i) τ))) -
      (∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
        A n i * (b (mesh T n (i+1)) - b (mesh T n i)) else 0)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let η : ℝ := ε / (K+1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hb) η hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((mesh_step_tendsto T).eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, ← Finset.sum_sub_distrib]
  have hbound : |∑ i ∈ Finset.range (2^n),
      (A n i * (b (min (mesh T n (i+1)) τ) - b (min (mesh T n i) τ)) -
        if mesh T n i < τ then A n i * (b (mesh T n (i+1)) - b (mesh T n i)) else 0)| ≤ K*η := by
    apply one_crossing_sum_bound (τ := τ) (mesh_mono T hT n) (mul_nonneg hK hη.le)
    · intro i hi hni
      rw [clipped_increment_eq (mesh_mono T hT n (Nat.le_succ i)) b hni]
      split_ifs <;> simp
    · intro i hi hc
      rw [min_eq_right hc.2.le, min_eq_left hc.1.le, ite_eq_left hc.1,
        ← mul_sub, sub_sub_sub_cancel_right, abs_mul]
      apply mul_le_mul (hA n i) _ (abs_nonneg _) hK
      have hd : dist τ (mesh T n (i+1)) < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hc.2.le)]
        have hs := mesh_step T n i
        have hnδ := hN n hn
        linarith [hc.1]
      exact (hmod τ ⟨hτ, hτT⟩ _ (mesh_mem T hT n (i+1) hi) hd).le
  apply hbound.trans_lt
  dsimp [η]
  rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0 < K+1)]
  nlinarith

lemma abs_sq_sub_sq_le {x y η : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hη : 0 ≤ η) (hxy : |x-y| ≤ η) : |x^2-y^2| ≤ 2*η := by
  calc
    _ = |x-y| * |x+y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ η * (|x|+|y|) := mul_le_mul hxy (abs_add_le _ _) (abs_nonneg _) hη
    _ ≤ η*(1+1) := mul_le_mul_of_nonneg_left (add_le_add hx hy) hη
    _ = _ := by ring

lemma clipped_quadraticSum_difference_tendsto {T τ : ℝ} (hT : 0 ≤ T)
    (_hτ : 0 ≤ τ) (_hτT : τ ≤ T) {b : ℝ → ℝ}
    (hb : ContinuousOn b (Icc 0 T)) (A : ℕ → ℕ → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ n i, |A n i| ≤ K) :
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (2^n), A n i *
        (b (min (mesh T n (i+1)) τ) - b (min (mesh T n i) τ))^2) -
      (∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
        A n i * (b (mesh T n (i+1)) - b (mesh T n i))^2 else 0)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let η : ℝ := ε / (2*K+1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hb) (min 1 η) (lt_min (by norm_num) hη)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((mesh_step_tendsto T).eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, ← Finset.sum_sub_distrib]
  have hbound : |∑ i ∈ Finset.range (2^n),
      (A n i * (b (min (mesh T n (i+1)) τ) - b (min (mesh T n i) τ))^2 -
        if mesh T n i < τ then A n i * (b (mesh T n (i+1)) - b (mesh T n i))^2 else 0)| ≤ K*(2*η) := by
    apply one_crossing_sum_bound (τ := τ) (mesh_mono T hT n) (by positivity)
    · intro i hi hni
      rw [clipped_increment_eq (mesh_mono T hT n (Nat.le_succ i)) b hni]
      split_ifs <;> simp
    · intro i hi hc
      have hdist (x y : ℝ) (hx : x ∈ Icc (mesh T n i) (mesh T n (i+1)))
          (hy : y ∈ Icc (mesh T n i) (mesh T n (i+1))) : dist x y < δ := by
        rw [Real.dist_eq, abs_lt]
        have hs := mesh_step T n i
        have hnδ := hN n hn
        constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
      have hmod' (x y : ℝ) (hx : x ∈ Icc (mesh T n i) (mesh T n (i+1)))
          (hy : y ∈ Icc (mesh T n i) (mesh T n (i+1))) :
          |b x-b y| ≤ min 1 η := by
        have hsub := Icc_subset_Icc (mesh_mem T hT n i hi.le).1 (mesh_mem T hT n (i+1) hi).2
        exact (hmod x (hsub hx) y (hsub hy) (hdist x y hx hy)).le
      have hcurr : mesh T n i ≤ mesh T n (i+1) := mesh_mono T hT n (Nat.le_succ i)
      have hτmem : τ ∈ Icc (mesh T n i) (mesh T n (i+1)) := ⟨hc.1.le,hc.2.le⟩
      have hx := (hmod' τ _ hτmem (left_mem_Icc.2 hcurr)).trans (min_le_left _ _)
      have hy := (hmod' _ _ (right_mem_Icc.2 hcurr) (left_mem_Icc.2 hcurr)).trans (min_le_left _ _)
      have hxy := (hmod' τ _ hτmem (right_mem_Icc.2 hcurr)).trans (min_le_right _ _)
      rw [min_eq_right hc.2.le, min_eq_left hc.1.le, ite_eq_left hc.1, ← mul_sub, abs_mul]
      apply mul_le_mul (hA n i) _ (abs_nonneg _) hK
      apply abs_sq_sub_sq_le hx hy hη.le
      simpa only [sub_sub_sub_cancel_right] using hxy
  apply hbound.trans_lt
  dsimp [η]
  rw [show K * (2 * (ε / (2*K+1))) = (2*K*ε)/(2*K+1) by ring,
    div_lt_iff₀ (by linarith : 0 < 2*K+1)]
  nlinarith

lemma clipped_mem {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 ≤ τ) (n i : ℕ) :
    min (mesh T n i) τ ∈ Icc 0 τ := by
  constructor
  · exact le_min (by unfold mesh; positivity) hτ
  · exact min_le_right _ _

lemma prestop_riemann_tendsto {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 ≤ τ) (hτT : τ ≤ T)
    {C : ℝ → ℝ} (hC : ContinuousOn C (Icc 0 τ)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      if mesh T n i < τ then C (mesh T n i) * (T / (2 : ℝ)^n) else 0) atTop
      (𝓝 (∫ t in (0 : ℝ)..τ, C t)) := by
  let p := clippedDyadic T τ hT hτ hτT
  have hriem := p.riemann_tendsto hC
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hC
  have hKn : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl,hτ⟩)
  have hdiff := clipped_timeSum_difference_tendsto (τ := τ) hT
    (fun n i => C (min (mesh T n i) τ)) hKn
    (fun n i => hK _ (clipped_mem hT hτ n i))
  have heq (n i : ℕ) :
      (if mesh T n i < τ then C (min (mesh T n i) τ) * (T / (2 : ℝ)^n) else 0) =
      (if mesh T n i < τ then C (mesh T n i) * (T / (2 : ℝ)^n) else 0) := by
    split_ifs with h
    · rw [min_eq_left h.le]
    · rfl
  simp only [heq] at hdiff
  have hh := hriem.sub hdiff
  simpa only [p, clippedDyadic, sub_sub_cancel, sub_zero] using hh

end SLEExactGauge.StoppedMeshes

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.PartitionMeshes.PartitionSequence
open SLEExactGauge.TaylorMeshes SLEExactGauge.TimeField

lemma family_remainder_tendsto_of_eventually_bounded {T : ℝ} (p : PartitionSequence T)
    {f : ℕ → ℕ → ℝ → ℝ} {b : ℝ → ℝ}
    (hf : ∀ n i, ContDiff ℝ 3 (f n i)) {V K : ℝ}
    (hb : ContinuousOn b (Icc 0 T)) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (h3 : ∀ n i x, |iteratedDeriv 3 (f n i) x| ≤ K)
    (hQ : ∀ᶠ n in atTop, (∑ i ∈ Finset.range (p.count n),
      (b (p.time n (i+1))-b (p.time n i))^2) ≤ V) :
    Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      remainder₂ (f n i) (b (p.time n i)) (b (p.time n (i+1)))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε / ((K+1)*(V+1))
  have hδ : 0 < δ := div_pos hε (mul_pos (by linarith) (by linarith))
  have hs := p.increments_small hb hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.and hQ)
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨hs, hq⟩
  have hr := sum_family_remainder₂_bound (hf n) (fun i => b (p.time n i))
    (p.count n) K δ hK hδ.le (fun i _ z _ => h3 n i z) (fun i hi => (hs i hi).le)
  simp only [Real.dist_eq, sub_zero]
  calc
    _ ≤ K * δ / 6 * ∑ i ∈ Finset.range (p.count n),
        (b (p.time n (i+1))-b (p.time n i))^2 := hr
    _ ≤ K * δ / 6 * (V+1) :=
      mul_le_mul_of_nonneg_left (hq.trans (by linarith)) (by positivity)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < (K+1)*(V+1) := mul_pos (by linarith) (by linarith)
      have hid : K * (ε / ((K+1)*(V+1))) / 6 * (V+1) = ε * (K / (6*(K+1))) := by
        field_simp
      rw [hid]
      have hk : K / (6*(K+1)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      simpa using mul_lt_mul_of_pos_left hk hε

end SLEExactGauge.PartitionMeshes.PartitionSequence

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.StoppedMeshes
open TaylorMeshes PartitionMeshes

lemma clipped_quadratic_eventually_bounded {T τ V : ℝ} (hT : 0 ≤ T)
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) {b : ℝ → ℝ} (hb : ContinuousOn b (Icc 0 T))
    (hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1)) - b (mesh T n i))^2) atTop (𝓝 V)) :
    ∀ᶠ n in atTop, (∑ i ∈ Finset.range (2^n),
      (b (min (mesh T n (i+1)) τ) - b (min (mesh T n i) τ))^2) ≤ V+2 := by
  have hd := clipped_quadraticSum_difference_tendsto hT hτ hτT hb
    (fun _ _ => 1) (by norm_num : (0 : ℝ) ≤ 1) (fun _ _ => by norm_num)
  simp only [one_mul] at hd
  filter_upwards [hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hQ.eventually (gt_mem_nhds (show V < V+1 by linarith))] with n hn hqn
  have hle : (∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
      (b (mesh T n (i+1)) - b (mesh T n i))^2 else 0) ≤
      ∑ i ∈ Finset.range (2^n), (b (mesh T n (i+1)) - b (mesh T n i))^2 := by
    apply Finset.sum_le_sum
    intro i hi
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  linarith

end SLEExactGauge.StoppedMeshes

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.BrownianStopped
open TaylorMeshes TimeField PartitionMeshes StoppedMeshes BrownianField

lemma coefficient_clipped_bound {T τ K : ℝ} (C : ℝ → ℝ)
    (hC : ∀ n i, mesh T n i < τ → |C (mesh T n i)| ≤ K) (n i : ℕ) :
    |C (min (mesh T n i) τ)| ≤ max K |C τ| := by
  by_cases h : mesh T n i < τ
  · rw [min_eq_left h.le]
    exact (hC n i h).trans (le_max_left _ _)
  · rw [min_eq_right (le_of_not_gt h)]
    exact le_max_right _ _

lemma stopped_field_taylor_limit {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 ≤ τ) (hτT : τ ≤ T)
    {F V : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hb : ContinuousOn b (Icc 0 T)) (hreg : FieldRegular F V b τ)
    (hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1)) - b (mesh T n i))^2) atTop (𝓝 T))
    {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hA : ∀ n i, mesh T n i < τ →
      |deriv (F (mesh T n i)) (b (mesh T n i))| ≤ K₁)
    (hC : ∀ n i, mesh T n i < τ →
      |iteratedDeriv 2 (F (mesh T n i)) (b (mesh T n i))| ≤ K₂)
    (hE : Tendsto (fun n => ∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
      iteratedDeriv 2 (F (mesh T n i)) (b (mesh T n i)) *
        ((b (mesh T n (i+1)) - b (mesh T n i))^2 - T/(2 : ℝ)^n) else 0) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
      deriv (F (mesh T n i)) (b (mesh T n i)) *
        (b (mesh T n (i+1)) - b (mesh T n i)) else 0) atTop
      (𝓝 (F τ (b τ) - F 0 (b 0) - (∫ t in (0 : ℝ)..τ, V t (b t)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..τ, iteratedDeriv 2 (F t) (b t))) := by
  let p := clippedDyadic T τ hT hτ hτT
  let C : ℝ → ℝ := fun t => iteratedDeriv 2 (F t) (b t)
  let A : ℝ → ℝ := fun t => deriv (F t) (b t)
  have hbτ := hb.mono (Icc_subset_Icc le_rfl hτT)
  have hQc := clipped_quadratic_eventually_bounded hT hτ hτT hb hQ
  obtain ⟨K₃, hK₃, h₃⟩ := hreg.third_bound
  have hr := p.family_remainder_tendsto_of_eventually_bounded
    (f := fun n i => F (p.time n i)) (fun _ _ => hreg.smooth _)
    hbτ (show 0 ≤ T+2 by linarith) hK₃ (fun _ _ x => h₃ _ x) hQc
  have htime := p.time_increment_tendsto hreg.time_cont hreg.time_deriv hreg.drift_cont
  have hriem := prestop_riemann_tendsto hT hτ hτT hreg.second_cont
  let Qpred : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
    C (mesh T n i) * (b (mesh T n (i+1)) - b (mesh T n i))^2 else 0
  have hQpred : Tendsto Qpred atTop (𝓝 (∫ t in (0 : ℝ)..τ, C t)) := by
    have heq (n : ℕ) : Qpred n =
      (∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
        C (mesh T n i) * ((b (mesh T n (i+1))-b (mesh T n i))^2-T/(2 : ℝ)^n) else 0) +
      (∑ i ∈ Finset.range (2^n), if mesh T n i < τ then C (mesh T n i)*(T/(2 : ℝ)^n) else 0) := by
      unfold Qpred
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    dsimp only [C] at heq
    simpa only [← heq, zero_add] using hE.add hriem
  have hQdiff := clipped_quadraticSum_difference_tendsto hT hτ hτT hb
    (fun n i => C (p.time n i))
    (K := max K₂ |C τ|) (hK₂.trans (le_max_left _ _))
    (coefficient_clipped_bound C hC)
  have hQeq (n i : ℕ) :
      (if mesh T n i < τ then C (p.time n i) *
        (b (mesh T n (i+1))-b (mesh T n i))^2 else 0) =
      (if mesh T n i < τ then C (mesh T n i) *
        (b (mesh T n (i+1))-b (mesh T n i))^2 else 0) := by
    split_ifs with h
    · simp only [p, clippedDyadic, min_eq_left h.le]
    · rfl
  simp only [hQeq] at hQdiff
  have hQweighted : Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      C (p.time n i) * (b (p.time n (i+1)) - b (p.time n i))^2) atTop
      (𝓝 (∫ t in (0 : ℝ)..τ, C t)) := by
    simpa only [Qpred, sub_add_cancel, zero_add, p, clippedDyadic] using hQdiff.add hQpred
  have hTel (n : ℕ) : ∑ i ∈ Finset.range (p.count n),
      (F (p.time n (i+1)) (b (p.time n (i+1))) -
        F (p.time n i) (b (p.time n i))) = F τ (b τ) - F 0 (b 0) := by
    rw [Finset.sum_range_sub (fun i => F (p.time n i) (b (p.time n i))), p.start, p.finish]
  have hIdentity (n : ℕ) : (∑ i ∈ Finset.range (p.count n),
      A (p.time n i)*(b (p.time n (i+1))-b (p.time n i))) =
      F τ (b τ) - F 0 (b 0) -
      (∑ i ∈ Finset.range (p.count n),
        (F (p.time n (i+1)) (b (p.time n (i+1))) -
          F (p.time n i) (b (p.time n (i+1))))) - (1/2 : ℝ)*
      (∑ i ∈ Finset.range (p.count n),
        C (p.time n i)*(b (p.time n (i+1))-b (p.time n i))^2) -
      (∑ i ∈ Finset.range (p.count n), remainder₂ (F (p.time n i))
        (b (p.time n i)) (b (p.time n (i+1)))) := by
    rw [← hTel n]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [A, C, remainder₂, iteratedDeriv_succ, iteratedDeriv_zero]
    ring
  have hAclip : Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      A (p.time n i)*(b (p.time n (i+1))-b (p.time n i))) atTop
      (𝓝 (F τ (b τ) - F 0 (b 0) - (∫ t in (0 : ℝ)..τ, V t (b t)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..τ, C t)) := by
    have hh := (((tendsto_const_nhds (x := F τ (b τ) - F 0 (b 0))).sub
      htime).sub (hQweighted.const_mul (1/2 : ℝ))).sub hr
    simpa only [← hIdentity, sub_zero] using hh
  have hAdiff := clipped_linearSum_difference_tendsto hT hτ hτT hb
    (fun n i => A (p.time n i))
    (K := max K₁ |A τ|) (hK₁.trans (le_max_left _ _))
    (coefficient_clipped_bound A hA)
  have hAeq (n i : ℕ) :
      (if mesh T n i < τ then A (p.time n i) *
        (b (mesh T n (i+1))-b (mesh T n i)) else 0) =
      (if mesh T n i < τ then A (mesh T n i) *
        (b (mesh T n (i+1))-b (mesh T n i)) else 0) := by
    split_ifs with h
    · simp only [p, clippedDyadic, min_eq_left h.le]
    · rfl
  simp only [hAeq] at hAdiff
  have hh := hAclip.sub hAdiff
  simpa only [p, clippedDyadic, A, C, sub_sub_cancel, sub_zero] using hh

end SLEExactGauge.BrownianStopped

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.BrownianStopped
open BrownianPredictable PredictableLimit BrownianIto TaylorMeshes BrownianField

def stoppedCoeff {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ) (F : Ω → ℝ → ℝ → ℝ) (n i : ℕ) (ω : Ω) : ℝ :=
  if mesh T n i < τ ω then
    iteratedDeriv k (F ω (mesh T n i)) (B (dyadicTime T n i) ω) else 0

theorem stopped_fieldSum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (τ : Ω → ℝ) (F V : Ω → ℝ → ℝ → ℝ)
    (hτ : ∀ᵐ ω ∂P, 0 ≤ τ ω ∧ τ ω ≤ T)
    (hreg : ∀ᵐ ω ∂P, FieldRegular (F ω) (V ω) (fun t => B t.toNNReal ω) (τ ω))
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (stoppedCoeff 2 B T τ F n i))
    (hC2 : ∀ n i, MemLp (stoppedCoeff 2 B T τ F n i) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ ω ∂P, |stoppedCoeff 2 B T τ F n i ω| ≤ K₂)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hAbound : ∀ n i, ∀ᵐ ω ∂P, |stoppedCoeff 1 B T τ F n i ω| ≤ K₁) :
    ∀ᵐ ω ∂P, Tendsto (fun n => dyadicDriverSum B T (stoppedCoeff 1 B T τ F) n ω) atTop
      (𝓝 (F ω (τ ω) (B (τ ω).toNNReal ω) - F ω 0 (B 0 ω) -
        (∫ t in (0 : ℝ)..(τ ω), V ω t (B t.toNNReal ω)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω),
          iteratedDeriv 2 (F ω t) (B t.toNNReal ω))) := by
  have he := brownian_dyadic_weighted_quadraticError_tendsto hB T
    (stoppedCoeff 2 B T τ F) hC hC2 K₂ hK₂ hbound
  have hC_all : ∀ᵐ ω ∂P, ∀ n i, |stoppedCoeff 2 B T τ F n i ω| ≤ K₂ :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hbound n))
  have hA_all : ∀ᵐ ω ∂P, ∀ n i, |stoppedCoeff 1 B T τ F n i ω| ≤ K₁ :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hAbound n))
  filter_upwards [hB.cont, quadraticSum_tendsto hB T, he, hreg, hτ, hC_all, hA_all]
    with ω hb hQ hE hr hτω hCω hAω
  let b : ℝ → ℝ := fun t => B t.toNNReal ω
  have hbc : Continuous b := hb.comp continuous_real_toNNReal
  have hQ' : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1))-b (mesh T n i))^2) atTop (𝓝 (T : ℝ)) := by
    simpa only [quadraticSum, b, mesh_toNNReal] using hQ
  have hE' : Tendsto (fun n => ∑ i ∈ Finset.range (2^n), if mesh T n i < τ ω then
      iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
        ((b (mesh T n (i+1))-b (mesh T n i))^2 - (T : ℝ)/(2 : ℝ)^n) else 0)
        atTop (𝓝 0) := by
    have heq (n : ℕ) : dyadicQuadraticError B T (stoppedCoeff 2 B T τ F) n ω =
        ∑ i ∈ Finset.range (2^n), if mesh T n i < τ ω then
          iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
            ((b (mesh T n (i+1))-b (mesh T n i))^2 - (T : ℝ)/(2 : ℝ)^n) else 0 := by
      unfold dyadicQuadraticError
      apply Finset.sum_congr rfl
      intro i hi
      simp only [stoppedCoeff, b, mesh_toNNReal]
      split_ifs <;> simp
    simpa only [heq] using hE
  have hA' (n i : ℕ) (hi : mesh T n i < τ ω) :
      |deriv (F ω (mesh T n i)) (b (mesh T n i))| ≤ K₁ := by
    simpa only [stoppedCoeff, ite_eq_left hi, iteratedDeriv_succ, iteratedDeriv_zero,
      b, mesh_toNNReal] using hAω n i
  have hC' (n i : ℕ) (hi : mesh T n i < τ ω) :
      |iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i))| ≤ K₂ := by
    simpa only [stoppedCoeff, ite_eq_left hi, b, mesh_toNNReal] using hCω n i
  have ht := stopped_field_taylor_limit T.coe_nonneg hτω.1 hτω.2 hbc.continuousOn
    hr hQ' hK₁ hK₂ hA' hC' hE'
  have heq (n : ℕ) : dyadicDriverSum B T (stoppedCoeff 1 B T τ F) n ω =
      ∑ i ∈ Finset.range (2^n), if mesh T n i < τ ω then
        deriv (F ω (mesh T n i)) (b (mesh T n i)) *
          (b (mesh T n (i+1))-b (mesh T n i)) else 0 := by
    unfold dyadicDriverSum
    apply Finset.sum_congr rfl
    intro i hi
    simp only [stoppedCoeff, b, mesh_toNNReal, iteratedDeriv_succ, iteratedDeriv_zero]
    split_ifs <;> simp
  simpa only [← heq, b, Real.toNNReal_zero] using ht

theorem stopped_field_ito_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (τ : Ω → ℝ) (F V : Ω → ℝ → ℝ → ℝ)
    (hτ : ∀ᵐ ω ∂P, 0 ≤ τ ω ∧ τ ω ≤ T)
    (hreg : ∀ᵐ ω ∂P, FieldRegular (F ω) (V ω) (fun t => B t.toNNReal ω) (τ ω))
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (stoppedCoeff 2 B T τ F n i))
    (hC2 : ∀ n i, MemLp (stoppedCoeff 2 B T τ F n i) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ ω ∂P, |stoppedCoeff 2 B T τ F n i ω| ≤ K₂)
    (hA : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (stoppedCoeff 1 B T τ F n i))
    (hA2 : ∀ n i, MemLp (stoppedCoeff 1 B T τ F n i) 2 P)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hAbound : ∀ n i, ∀ᵐ ω ∂P, |stoppedCoeff 1 B T τ F n i ω| ≤ K₁) :
    let Y := fun ω => F ω (τ ω) (B (τ ω).toNNReal ω) - F ω 0 (B 0 ω) -
      (∫ t in (0 : ℝ)..(τ ω), V ω t (B t.toNNReal ω)) -
      (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω), iteratedDeriv 2 (F ω t) (B t.toNNReal ω)
    Integrable Y P ∧ (∫ ω, Y ω ∂P) = 0 := by
  dsimp only
  exact limit_centered hB T (stoppedCoeff 1 B T τ F) hA hA2 K₁ hK₁ hAbound _
    (stopped_fieldSum_tendsto hB T τ F V hτ hreg hC hC2 K₂ hK₂ hbound K₁ hK₁ hAbound)

end SLEExactGauge.BrownianStopped

end

end

end

end

end

end OAI
