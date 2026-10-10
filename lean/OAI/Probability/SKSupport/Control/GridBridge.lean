import Mathlib
import OAI.Probability.SKSupport.Regularity.AbsExtend
import OAI.Probability.SKSupport.Foundations.FiniteValue
import OAI.Probability.SKSupport.Control.VariableGrid

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def remainingLengths (h : ℝ≥0) (t : ℝ) (j : ℕ) : ℝ≥0 :=
  Real.toNNReal (min (h:ℝ) (((j+1:ℕ):ℝ)*h-t))

lemma remainingLengths_shift (h : ℝ≥0) (t : ℝ) (j : ℕ) :
    remainingLengths h t (j+1) = remainingLengths h (t-h) j := by
  unfold remainingLengths
  congr 2
  push_cast
  ring

lemma remainingLengths_nonpos (h : ℝ≥0) {t : ℝ} (ht : t ≤ 0) (j : ℕ) :
    remainingLengths h t j = h := by
  have hh : (h:ℝ) ≤ ((j+1:ℕ):ℝ)*h-t := by
    push_cast
    nlinarith [h.coe_nonneg, mul_nonneg (Nat.cast_nonneg (α := ℝ) j) h.coe_nonneg]
  unfold remainingLengths
  rw [min_eq_left hh]
  exact Real.toNNReal_coe

lemma remainingLengths_head (h : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) :
    remainingLengths h t 0 = Real.toNNReal ((h:ℝ)-t) := by
  simp only [remainingLengths,Nat.zero_add,Nat.cast_one,one_mul]
  rw [min_eq_right (by linarith)]

lemma remainingLengths_time (h : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Nonuniform.time (remainingLengths h t) n = Real.toNNReal ((n:ℝ)*h-t) := by
  induction n with
  | zero => simp only [Nonuniform.time_zero,Nat.cast_zero,zero_mul,zero_sub]
            rw [Real.toNNReal_of_nonpos (by linarith)]
  | succ n ih =>
    rw [Nonuniform.time_succ,ih]
    apply NNReal.coe_injective
    simp only [NNReal.coe_add,remainingLengths,Real.coe_toNNReal']
    push_cast
    have hn := h.coe_nonneg
    by_cases hc : (n:ℝ)*h ≤ t
    · rw [max_eq_right (by linarith)]
      have hm : ((n:ℝ)+1)*h-t ≤ h := by nlinarith
      rw [min_eq_right hm,zero_add]
    · have hp : 0 ≤ (n:ℝ)*h-t := by linarith
      rw [max_eq_left hp,min_eq_left (by nlinarith),max_eq_left hn,
        max_eq_left (by nlinarith)]
      ring

lemma cascadeV_shift (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (n k j : ℕ) :
    cascadeV (fun l => h (k+l)) (fun l => c (k+l)) f n j = cascadeV h c f n (k+j) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [cascadeV,ih]
    rw [Nat.add_assoc]

lemma cascadeV_uniform (h : ℝ≥0) (c : ℕ → ℝ≥0) (f : ℝ → ℝ) (n k : ℕ) :
    cascadeV (fun _ => h) c f n k = cascade c h f n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [cascadeV,cascade,ih]

lemma finiteValue_eq_remaining {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (n i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    finiteValue c h f n i t = cascadeV (remainingLengths h t) (fun j => c (i+j)) f n 0 := by
  induction n generalizing i t with
  | zero => rfl
  | succ n ih =>
    have hs : cascadeV (remainingLengths h t) (fun j => c (i+j)) f n 1 =
        cascadeV (remainingLengths h (t-h)) (fun j => c ((i+1)+j)) f n 0 := by
      have he := cascadeV_shift (remainingLengths h t) (fun j => c (i+j)) f n 1 0
      simp only [Nat.add_zero] at he
      rw [← he]
      congr 2
      · funext j
        rw [Nat.add_comm 1 j,remainingLengths_shift]
      · funext j
        congr 1
        omega
    by_cases hth : t ≤ h
    · rw [finiteValue_head f c h n i hth]
      have hl : remainingLengths h (t-h) = fun _ => h := by
        funext j
        exact remainingLengths_nonpos h (sub_nonpos.mpr hth) j
      funext x
      simp only [cascadeV,Nat.add_zero]
      rw [hs,hl,cascadeV_uniform]
      have hc := cascadeV_shift (fun _ => h) c f n (i+1) 0
      simp only [Nat.add_zero,cascadeV_uniform] at hc
      rw [hc]
      rw [remainingLengths_head h ht]
      exact varianceLogHeat_eq_logSemigroup_toNNReal
        (cascade_regular hf hLip c h n (i+1)).smooth.continuous.measurable (c i) (h-t) x
    · rw [finiteValue_tail f c h n i (lt_of_not_ge hth),ih (i+1) (by linarith)]
      funext x
      simp only [cascadeV,Nat.add_zero]
      rw [hs,remainingLengths_head h ht,Real.toNNReal_of_nonpos (by linarith)]
      simp only [logSemigroup,semigroup,gaussianReal_zero_var,integral_dirac,add_zero]
      split_ifs with hc
      · rfl
      · rw [Real.log_exp,mul_div_cancel_left₀ _ (by exact_mod_cast hc)]

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def gridError (h c : ℕ → ℝ≥0) (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ∫ r in (time h k:ℝ)..(time h (k+1):ℝ), |(c k:ℝ)-g r|

lemma grid_integral_error (h c : ℕ → ℝ≥0) {g a : ℝ → ℝ}
    (hg : Integrable g) (ha : Measurable a) (hab : ∀ r, |a r| ≤ 1) (N : ℕ) :
    |(∑ k ∈ Finset.range N, ∫ r in (time h k:ℝ)..(time h (k+1):ℝ), (c k:ℝ)*a r) -
      ∫ r in (0:ℝ)..(time h N:ℝ), g r*a r| ≤ gridError h c g N := by
  have hga : Integrable (fun r => g r*a r) := hg.mul_bdd ha.aestronglyMeasurable
    (Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hab))
  have haI (k : ℕ) : IntervalIntegrable a volume (time h k:ℝ) (time h (k+1):ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast time_mono h (Nat.le_succ k))]
    exact Integrable.of_bound ha.aestronglyMeasurable 1
      (Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hab))
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => (time h k:ℝ)) (n := N) (fun k _ => hga.intervalIntegrable)
  simp only [time_zero,NNReal.coe_zero] at hs
  rw [← hs,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [← intervalIntegral.integral_sub ((haI k).const_mul _) hga.intervalIntegrable]
  have hc : IntervalIntegrable (fun r => |(c k:ℝ)-g r|) volume (time h k:ℝ) (time h (k+1):ℝ) :=
    (intervalIntegrable_const.sub hg.intervalIntegrable).abs
  change ‖∫ r in (time h k:ℝ)..(time h (k+1):ℝ), (c k:ℝ)*a r-g r*a r‖ ≤ _
  apply intervalIntegral.norm_integral_le_of_norm_le
    (by exact_mod_cast time_mono h (Nat.le_succ k)) _ hc
  filter_upwards [] with r hr
  rw [← sub_mul,Real.norm_eq_abs,abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hab r) (abs_nonneg ((c k:ℝ)-g r))

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Control.elapsed_integral (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (α : Control W (Real.toNNReal t)) (ξ : Ω) (p : ℕ) :
    (∫ r in (0:ℝ)..(1-t), extend γ.val (t+r)*(α.val (Real.toNNReal r) ξ)^p) =
      ∫ s in t..1, extend γ.val s*(α.val (Real.toNNReal (s-t)) ξ)^p := by
  have he := intervalIntegral.integral_comp_add_left
    (fun s => extend γ.val s*(α.val (Real.toNNReal (s-t)) ξ)^p) t (a := 0) (b := 1-t)
  simpa only [add_sub_cancel_left,add_zero,add_sub_cancel] using he

lemma profit_eq_integral {B α : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsPreBrownianReal B P)
    (ham : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2)) (hab : ∀ t ξ, |α t ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) {f : ℝ → ℝ} (hf : LipschitzWith 1 f) (x : ℝ) (N : ℕ) :
    profit (P := P) B α h c f x N = ∫ ξ, f (controlled B α h c x N ξ)-
      ∑ k ∈ Finset.range N, stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ ∂P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hi := controlled_integrable hB ham hab h c x N
  have hfI : Integrable (fun ξ => f (controlled B α h c x N ξ)) P := by
    apply ((integrable_const |f 0|).add hi.norm).mono'
      (hf.continuous.comp_aestronglyMeasurable hi.aestronglyMeasurable)
    filter_upwards [] with ξ
    have hh := hf.dist_le_mul (controlled B α h c x N ξ) 0
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_zero] at hh
    change |f (controlled B α h c x N ξ)| ≤ |f 0|+|controlled B α h c x N ξ|
    have htri := abs_sub_le (f (controlled B α h c x N ξ)) (f 0) 0
    simp only [sub_zero] at htri
    linarith
  have hiC (k : ℕ) : Integrable (stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k)) P :=
    stepCost_integrable (ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd))
      (fun r ξ => hab _ ξ) _ _ _ (h k).coe_nonneg (c k).coe_nonneg
  rw [integral_sub hfI (integrable_finsetSum (Finset.range N) (fun k _ => hiC k)),integral_finsetSum _ (fun k _ => hiC k)]
  rfl

lemma control_profit_error (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (α : Control W (Real.toNNReal t))
    (h c : ℕ → ℝ≥0) (N : ℕ) (hH : (time h N:ℝ) = 1-t)
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) {ε : ℝ} (he : ∀ z, |f z - abs z| ≤ ε) :
    |profit (P := W.law) (fun s ξ => W.B (Real.toNNReal t+s) ξ-W.B (Real.toNNReal t) ξ)
      α.val h c f x N - ∫ ξ, controlPayoff W γ t x α ξ ∂W.law| ≤
      ε+(3/2:ℝ)*gridError h c (fun r => extend γ.val (t+r)) N := by
  let := W.isProbability
  let B := fun s ξ => W.B (Real.toNNReal t+s) ξ-W.B (Real.toNNReal t) ξ
  have hB : IsPreBrownianReal B W.law := W.brownian.toIsPreBrownianReal.shift _
  have hpred : Real.toNNReal t+time h N = 1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add,Real.coe_toNNReal _ ht0,hH,NNReal.coe_one]
    ring
  have hg : Integrable (fun r => extend γ.val (t+r)) := γ.integrable.comp_add_left t
  have ham : Measurable (fun p : ℝ × Ω => α.val (Real.toNNReal p.1) p.2) :=
    α.measurable.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  let E := gridError h c (fun r => extend γ.val (t+r)) N
  have hpath (ξ : Ω) :
      |(f (controlled B α.val h c x N ξ)-∑ k ∈ Finset.range N,
        stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k) ξ)-
        controlPayoff W γ t x α ξ| ≤ ε+(3/2:ℝ)*E := by
    have hamξ : Measurable (fun r => α.val (Real.toNNReal r) ξ) := ham.comp measurable_prodMk_right
    have hd := grid_integral_error h c hg hamξ
      (fun r => α.bound _ ξ) N
    have hc := grid_integral_error h c hg (hamξ.pow_const 2)
      (fun r => by simpa only [abs_pow,one_pow] using
        pow_le_pow_left₀ (abs_nonneg (α.val (Real.toNNReal r) ξ)) (α.bound _ ξ) 2) N
    rw [hH,Control.elapsed_integral W γ t α ξ 2] at hc
    have hdp := Control.elapsed_integral W γ t α ξ 1
    simp only [pow_one] at hdp
    rw [hH,hdp] at hd
    have hstate : |controlled B α.val h c x N ξ-
        (x+W.B 1 ξ-W.B (Real.toNNReal t) ξ+
          ∫ s in t..1, extend γ.val s*α.val (Real.toNNReal (s-t)) ξ)| ≤ E := by
      rw [controlled_formula]
      simp only [B,hpred,add_zero,sub_self,sub_zero,stepDrift,← coe_time_succ]
      convert hd using 1
      simp only [sub_eq_add_neg,add_assoc]
      congr 1
      ring
    have hferr := (abs_sub_le (f (controlled B α.val h c x N ξ))
      |controlled B α.val h c x N ξ|
      |x+W.B 1 ξ-W.B (Real.toNNReal t) ξ+
        ∫ s in t..1, extend γ.val s*α.val (Real.toNNReal (s-t)) ξ|).trans
        (add_le_add (he _) ((abs_abs_sub_abs_le_abs_sub _ _).trans hstate))
    have hcost : |(∑ k ∈ Finset.range N, stepCost (fun r => α.val (Real.toNNReal r))
        (time h k) (h k) (c k) ξ)-(1/2:ℝ)*∫ s in t..1,
          extend γ.val s*(α.val (Real.toNNReal (s-t)) ξ)^2| ≤ (1/2:ℝ)*E := by
      simp only [stepCost,← coe_time_succ,← Finset.mul_sum,← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      exact mul_le_mul_of_nonneg_left hc (by norm_num)
    unfold controlPayoff
    have hp := abs_sub_le (f (controlled B α.val h c x N ξ)-∑ k ∈ Finset.range N,
      stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k) ξ)
      (|x+W.B 1 ξ-W.B (Real.toNNReal t) ξ+
        ∫ s in t..1, extend γ.val s*α.val (Real.toNNReal (s-t)) ξ|-
        ∑ k ∈ Finset.range N, stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k) ξ)
      (|x+W.B 1 ξ-W.B (Real.toNNReal t) ξ+
        ∫ s in t..1, extend γ.val s*α.val (Real.toNNReal (s-t)) ξ|-
        (1/2:ℝ)*∫ s in t..1, extend γ.val s*(α.val (Real.toNNReal (s-t)) ξ)^2)
    simp only [sub_sub_sub_cancel_right,sub_sub_sub_cancel_left,abs_sub_comm] at hp
    linarith
  rw [profit_eq_integral hB α.measurable α.bound h c hf x N]
  have hi := controlled_integrable hB α.measurable α.bound h c x N
  have hfI : Integrable (fun ξ => f (controlled B α.val h c x N ξ)) W.law := by
    apply ((integrable_const (|f 0|)).add hi.norm).mono'
      (hf.continuous.comp_aestronglyMeasurable hi.aestronglyMeasurable)
    filter_upwards [] with ξ
    have hh := hf.dist_le_mul (controlled B α.val h c x N ξ) 0
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_zero] at hh
    change |f (controlled B α.val h c x N ξ)| ≤ |f 0|+|controlled B α.val h c x N ξ|
    have htri := abs_sub_le (f (controlled B α.val h c x N ξ)) (f 0) 0
    simp only [sub_zero] at htri
    linarith
  have hiC (k : ℕ) : Integrable (stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k)) W.law :=
    stepCost_integrable ham (fun r ξ => α.bound _ ξ) _ _ _ (h k).coe_nonneg (c k).coe_nonneg
  have hdiff := integral_sub (hfI.sub (integrable_finsetSum (Finset.range N) (fun k _ => hiC k)))
    (controlPayoff_integrable W γ t x ht1 α)
  simp only [Pi.sub_apply] at hdiff
  rw [← hdiff]
  have hn := norm_integral_le_of_norm_le_const (μ := W.law)
    (f := fun ξ => (f (controlled B α.val h c x N ξ)-∑ k ∈ Finset.range N,
      stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k) ξ)-
      controlPayoff W γ t x α ξ)
    (Eventually.of_forall (fun ξ => by simpa only [Real.norm_eq_abs] using hpath ξ))
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using hn

end ZeroTemperatureSK

end
end

end OAI
