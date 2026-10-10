import Mathlib
import OAI.Probability.SKSupport.Control.ExpectedControlPayoff
import OAI.Probability.SKSupport.Control.GridBridge

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

lemma finiteCoeff_cell (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i k : ℕ) (hk : k < N)
    {r : ℝ} (hr0 : 0 < r) (hrh : r ≤ h) :
    finiteCoeff c h N i ((k:ℝ)*h+r) = c (i+k) := by
  induction N generalizing i k with
  | zero => omega
  | succ N ih =>
    cases k with
    | zero => simp only [Nat.cast_zero,zero_mul,zero_add,finiteCoeff,ite_eq_left hrh,Nat.add_zero]
    | succ k =>
      have hgt : (h:ℝ) < ((k+1:ℕ):ℝ)*h+r := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) h.coe_nonneg]
      simp only [finiteCoeff,ite_eq_right (not_le.mpr hgt)]
      have he : ((k+1:ℕ):ℝ)*h+r-h = (k:ℝ)*h+r := by push_cast; ring
      rw [he,ih (i+1) k (by omega), show i+1+k = i+(k+1) by omega]

lemma finiteCoeff_intervalIntegrable (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (a b : ℝ) :
    IntervalIntegrable (finiteCoeff c h N i) volume a b := by
  obtain ⟨C,hC⟩ := finiteCoeff_bounds c h N i
  apply (intervalIntegrable_const (c := (C:ℝ))).mono_fun'
    (measurable_finiteCoeff c h N i).aestronglyMeasurable
  filter_upwards [] with r
  rw [Real.norm_eq_abs,abs_of_nonneg (hC r).1]
  exact (hC r).2

lemma finiteCoeff_remaining_cell (c : ℕ → ℝ≥0) (h : ℝ≥0) (N k : ℕ) (hk : k < N)
    {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Ioo (time (remainingLengths h t) k:ℝ)
      (time (remainingLengths h t) (k+1):ℝ)) :
    finiteCoeff c h N 0 (t+r) = c k := by
  rw [remainingLengths_time h ht,remainingLengths_time h ht] at hr
  simp only [Real.coe_toNNReal',Set.mem_Ioo] at hr
  obtain ⟨hrlo,hrhi⟩ := hr
  have hkr : (k:ℝ)*h < t+r := by linarith [hrlo,le_max_left ((k:ℝ)*h-t) 0]
  have hrpos : 0 < r := (le_max_right ((k:ℝ)*h-t) 0).trans_lt hrlo
  have htkr : 0 < ((k+1:ℕ):ℝ)*h-t := by
    by_contra hn
    rw [max_eq_right (le_of_not_gt hn)] at hrhi
    linarith
  have hrr : t+r ≤ ((k+1:ℕ):ℝ)*h := by
    rw [max_eq_left htkr.le] at hrhi
    linarith
  have hloc : t+r-(k:ℝ)*h ≤ h := by push_cast at hrr; nlinarith
  have he := finiteCoeff_cell c h N 0 k hk (sub_pos.mpr hkr) hloc
  simp only [Nat.zero_add] at he
  simpa only [add_sub_cancel] using he

lemma finiteCoeff_nonneg (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t : ℝ) :
    0 ≤ finiteCoeff c h N i t := by
  obtain ⟨C,hC⟩ := finiteCoeff_bounds c h N i
  exact (hC t).1

lemma finiteCoeff_sample (c : ℕ → ℝ≥0) {h : ℝ≥0} (_hh : 0 < h) (N i : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (htN : t ≤ (N:ℝ)*h) (hN : 0 < N) :
    ∃ j < N, finiteCoeff c h N i t = c (i+j) ∧
      (j:ℝ)*h ≤ t ∧ t ≤ (j+1:ℕ)*h := by
  induction N generalizing i t with
  | zero => omega
  | succ N ih =>
    by_cases hth : t ≤ h
    · refine ⟨0,by omega,?_,?_,?_⟩
      · simp only [finiteCoeff,ite_eq_left hth,Nat.add_zero]
      · simpa using ht0
      · simpa using hth
    · have hNp : 0 < N := by
        by_contra hn
        have : N = 0 := by omega
        subst N
        norm_num at htN
        exact hth htN
      have htt : t-h ≤ (N:ℝ)*h := by push_cast at htN; nlinarith
      obtain ⟨j,hj,he,hl,hu⟩ := ih (i+1) (by linarith) htt hNp
      refine ⟨j+1,by omega,?_,?_,?_⟩
      · simp only [finiteCoeff,ite_eq_right hth,he]
        rw [show i+1+j = i+(j+1) by omega]
      · push_cast
        linarith
      · push_cast at hu ⊢
        nlinarith

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

lemma gridError_remaining (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) (hN : (N:ℝ)*h = 1)
    (γ : OrderParameter) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gridError (remainingLengths h t) c (fun r => extend γ.val (t+r)) N =
      ∫ s in t..1, |finiteCoeff c h N 0 s-extend γ.val s| := by
  let d := remainingLengths h t
  let g := fun r => |finiteCoeff c h N 0 (t+r)-extend γ.val (t+r)|
  have hH : (time d N:ℝ) = 1-t := by
    rw [remainingLengths_time h ht0,hN,Real.coe_toNNReal _ (by linarith)]
  have hg (a b : ℝ) : IntervalIntegrable g volume a b := by
    have hh := ((finiteCoeff_intervalIntegrable c h N 0 (t+a) (t+b)).sub
      γ.integrable.intervalIntegrable).abs.comp_add_left t
    simpa only [add_sub_cancel_left] using hh
  have he : gridError d c (fun r => extend γ.val (t+r)) N =
      ∑ k ∈ Finset.range N, ∫ r in (time d k:ℝ)..(time d (k+1):ℝ), g r := by
    apply Finset.sum_congr rfl
    intro k hk
    apply intervalIntegral.integral_congr_Ioo_of_le
      (by exact_mod_cast time_mono d (Nat.le_succ k))
    intro r hr
    dsimp only [g]
    rw [finiteCoeff_remaining_cell c h N k (Finset.mem_range.mp hk) ht0 hr]
  rw [he,intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hg _ _),time_zero,NNReal.coe_zero,hH]
  have hs := intervalIntegral.integral_comp_add_left
    (fun s => |finiteCoeff c h N 0 s-extend γ.val s|) t (a := 0) (b := 1-t)
  simpa only [add_zero,add_sub_cancel] using hs

lemma gridError_remaining_le (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) (hN : (N:ℝ)*h = 1)
    (γ : OrderParameter) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gridError (remainingLengths h t) c (fun r => extend γ.val (t+r)) N ≤
      ∫ s in (0:ℝ)..1, |finiteCoeff c h N 0 s-extend γ.val s| := by
  rw [gridError_remaining c h N hN γ ht0 ht1]
  exact intervalIntegral.integral_mono_interval ht0 ht1 le_rfl
    (Eventually.of_forall (fun s => abs_nonneg _))
    (((finiteCoeff_intervalIntegrable c h N 0 0 1).sub γ.integrable.intervalIntegrable).abs)

variable {Ω : Type*} [MeasurableSpace Ω]

lemma cascadeV_value_error (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h c : ℕ → ℝ≥0) (N : ℕ)
    (hH : (time h N:ℝ) = 1-t) {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {ε : ℝ} (he : ∀ z, |f z-abs z| ≤ ε) :
    |cascadeV h c f N 0 x-value W γ t x| ≤
      ε+(3/2:ℝ)*gridError h c (fun r => extend γ.val (t+r)) N := by
  let B := fun s ξ => W.B (Real.toNNReal t+s) ξ-W.B (Real.toNNReal t) ξ
  have hB : IsPreBrownianReal B W.law := W.brownian.toIsPreBrownianReal.shift _
  have hm (s : ℝ≥0) : Measurable (B s) := (W.measurable _).sub (W.measurable _)
  let E := ε+(3/2:ℝ)*gridError h c (fun r => extend γ.val (t+r)) N
  have hobj : ∀ v ∈ objectives (P := W.law) hm h c f x N, v ≤ value W γ t x+E := by
    intro v hv
    obtain ⟨a,hap,hab,rfl⟩ := hv
    let α : Control W (Real.toNNReal t) := ⟨a,hap,hab⟩
    have hh := control_profit_error W γ t x ht0 ht1 α h c N hH hLip he
    have hp := expected_controlPayoff_le_value W γ t x ht1 α
    have := (abs_le.mp hh).2
    change profit (P := W.law) B a h c f x N -
      (∫ ξ, controlPayoff W γ t x α ξ ∂W.law) ≤ E at this
    linarith
  have hb : BddAbove (objectives (P := W.law) hm h c f x N) := ⟨_,hobj⟩
  have hc := cascadeV_eq_control_sup hB hm hf hLip h c N x
  have hu : cascadeV h c f N 0 x ≤ value W γ t x+E := by
    rw [hc]
    exact csSup_le (objectives_nonempty hm h c f x N) hobj
  change |cascadeV h c f N 0 x-value W γ t x| ≤ E
  apply abs_sub_le_iff.mpr
  refine ⟨by linarith,?_⟩
  have hl : value W γ t x ≤ cascadeV h c f N 0 x+E := by
    unfold value
    refine csSup_le ⟨_,⟨zeroControl W (Real.toNNReal t),rfl⟩⟩ ?_
    rintro y ⟨α,rfl⟩
    have hh := control_profit_error W γ t x ht0 ht1 α h c N hH hLip he
    have hmem : profit (P := W.law) B α.val h c f x N ∈ objectives (P := W.law) hm h c f x N :=
      ⟨α.val,α.progressive,α.bound,rfl⟩
    have hp := le_csSup hb hmem
    rw [← hc] at hp
    have hh' := (abs_le.mp hh).1
    change -E ≤ profit (P := W.law) B α.val h c f x N -
      (∫ ξ, controlPayoff W γ t x α ξ ∂W.law) at hh'
    linarith
  linarith

theorem finiteValue_control_error (W : BrownianSystem Ω) (γ : OrderParameter)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) (hN : (N:ℝ)*h = 1)
    {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    {ε : ℝ} (he : ∀ z, |f z-abs z| ≤ ε) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |finiteValue c h f N 0 t x-value W γ t x| ≤
      ε+(3/2:ℝ)*∫ s in (0:ℝ)..1, |finiteCoeff c h N 0 s-extend γ.val s| := by
  rw [finiteValue_eq_remaining hf hLip c h N 0 ht0]
  simp only [Nat.zero_add]
  have hH : (time (remainingLengths h t) N:ℝ) = 1-t := by
    rw [remainingLengths_time h ht0,hN,Real.coe_toNNReal _ (by linarith)]
  exact (cascadeV_value_error W γ t x ht0 ht1 (remainingLengths h t) c N hH hf hLip he).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (gridError_remaining_le c h N hN γ ht0 ht1)
      (by norm_num : (0:ℝ) ≤ 3/2)))

end ZeroTemperatureSK

end
end

end OAI
