import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set
namespace YauCounterexamples

def radialBaseEnvelope (t r : ℝ) : ℝ := Real.log t+r^2-t^2

lemma log_upper_three_tenths {t : ℝ} (ht : 0 < t) (hT : t ≤ 3/10) :
    Real.log t < -1 := by
  have hq : t < (3/4 : ℝ)^4 := by norm_num at *; linarith
  have hlog := Real.log_lt_log ht hq
  rw [Real.log_pow] at hlog
  have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3/4 by norm_num)
  norm_num at hlog hh
  linarith

lemma radialBaseEnvelope_inside {t r : ℝ} (ht : 0 < t) (hT : t ≤ 3/10)
    (hr : 0 < r) (hrt : r < t) : Real.log r < radialBaseEnvelope t r := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hr ht)
  rw [Real.log_div hr.ne' ht.ne'] at hlog
  have hsq : t*t ≤ (3/10 : ℝ)*(3/10) := mul_self_le_mul_self ht.le hT
  have hmul : t*r ≤ (3/10 : ℝ)*(3/10) :=
    mul_le_mul hT (hrt.le.trans hT) hr.le (by norm_num)
  have hbound : t*(t+r) < 1 := by nlinarith
  have hfac : 0 < (t-r)*(1-t*(t+r)) := mul_pos (sub_pos.mpr hrt) (sub_pos.mpr hbound)
  have hrat : r/t-1 < r^2-t^2 := by
    apply sub_lt_iff_lt_add.mpr
    apply (div_lt_iff₀ ht).mpr
    nlinarith
  dsimp [radialBaseEnvelope]
  linarith

lemma radialBaseEnvelope_outside {t r : ℝ} (ht : 0 < t) (hT : t ≤ 3/10)
    (htr : t < r) (hr : r ≤ 1) : radialBaseEnvelope t r < Real.log r := by
  have ht1 : t < 1 := by linarith
  have hr0 : 0 < r := ht.trans htr
  have htsq : t^2 < 1 := by nlinarith
  have hrsq : r^2 ≤ 1 := by nlinarith
  have htrs : t^2 < r^2 := by nlinarith
  let A := (1-r^2)/(1-t^2)
  let B := (r^2-t^2)/(1-t^2)
  have hden : 0 < 1-t^2 := sub_pos.mpr htsq
  have hA : 0 ≤ A := div_nonneg (by linarith) hden.le
  have hB : 0 < B := div_pos (sub_pos.mpr htrs) hden
  have hsum : A+B=1 := by dsimp [A,B]; field_simp; ring
  have harg : A*t^2+B*1=r^2 := by dsimp [A,B]; field_simp; ring
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2
    (show t^2 ∈ Ioi (0 : ℝ) by exact sq_pos_of_pos ht)
    (show (1 : ℝ) ∈ Ioi (0 : ℝ) by norm_num) hA hB.le hsum
  simp only [smul_eq_mul, harg,Real.log_one,mul_zero,add_zero,Real.log_pow,
    Nat.cast_ofNat] at hlog
  have hbase : Real.log t+1-t^2 < 0 := by
    have hh := log_upper_three_tenths ht hT
    nlinarith [sq_nonneg t]
  have hneg := mul_neg_of_pos_of_neg hB hbase
  have hscale : B*(1-t^2)=r^2-t^2 := by dsimp [B]; field_simp
  dsimp [radialBaseEnvelope]
  nlinarith

lemma radialBaseEnvelope_boundary (t : ℝ) : radialBaseEnvelope t t = Real.log t := by
  simp [radialBaseEnvelope]

theorem radialBaseEnvelope_uniform_sign_margin :
    ∃ η > 0, ∀ t ∈ Icc (1/5 : ℝ) (3/10), ∀ r ∈ Icc (1/20 : ℝ) (1/8),
      η < radialBaseEnvelope t r-Real.log r := by
  let K : Set (ℝ × ℝ) := Icc (1/5 : ℝ) (3/10) ×ˢ Icc (1/20 : ℝ) (1/8)
  let F := fun q : ℝ × ℝ => radialBaseEnvelope q.1 q.2-Real.log q.2
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hne : K.Nonempty := ⟨(1/5,1/20),by norm_num [K]⟩
  have hc : ContinuousOn F K := by
    apply ContinuousOn.sub
    · exact ((Real.continuousOn_log.comp continuousOn_fst
        (fun q hq => (show q.1 ≠ 0 by have := hq.1.1; change q.1 ≠ 0; linarith))).add
        (continuousOn_snd.pow 2)).sub (continuousOn_fst.pow 2)
    · exact Real.continuousOn_log.comp continuousOn_snd
        (fun q hq => (show q.2 ≠ 0 by have := hq.2.1; change q.2 ≠ 0; linarith))
  obtain ⟨q,hq,hmin⟩ := hK.exists_isMinOn hne hc
  have hp : 0 < F q := by
    have hh := radialBaseEnvelope_inside (t := q.1) (r := q.2)
      (by have := hq.1.1; linarith) hq.1.2 (by have := hq.2.1; linarith)
      (by have := hq.1.1; have := hq.2.2; linarith)
    exact sub_pos.mpr hh
  refine ⟨F q/2,by positivity,?_⟩
  intro t ht r hr
  exact (half_lt_self hp).trans_le (hmin (show (t,r) ∈ K from ⟨ht,hr⟩))

end YauCounterexamples

end

end OAI
