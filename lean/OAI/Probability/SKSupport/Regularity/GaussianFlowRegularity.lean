import Mathlib
import OAI.Probability.SKSupport.Regularity.FamilyDifferentiation

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BoundedSmoothFamily.continuousOn_iteratedDeriv {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hF : BoundedSmoothFamily F)
    (hc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (S ×ˢ univ)) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => _root_.iteratedDeriv n (F p.1) p.2) (S ×ˢ univ) := by
  induction n with
  | zero => exact hc
  | succ n hn =>
    obtain ⟨C,hC⟩ := (hF.iteratedDeriv n).deriv.deriv.bound
    simpa only [iteratedDeriv_succ] using continuousOn_deriv_family hn
      (fun t _ => ((hF.iteratedDeriv n).regular t).smooth.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) C.coe_nonneg
      (fun t _ x => hC t x)

lemma varianceGradient_family {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    BoundedSmoothFamily (fun t => deriv (varianceLogHeat c t f)) := by
  have hm : Measurable (fun p : ℝ × ℝ => varianceLogHeat c p.1 f p.2) := by
    have hh := (measurable_backward hf.smooth.continuous.measurable c 0).comp
      (measurable_fst.neg.prodMk measurable_snd)
    simpa only [Function.comp_def,Pi.neg_apply,backward,zero_sub,neg_neg] using hh
  refine ⟨measurable_spatial_deriv hm (fun t =>
    (regularDatum_varianceLogHeat hf hLip hc t).smooth.differentiable (by simp)),
    fun t => (regularDatum_varianceLogHeat hf hLip hc t).deriv_bounded,?_⟩
  intro n
  simpa only [iteratedDeriv_succ'] using uniform_varianceLogHeat_derivative_bounds hf hLip hc n

lemma varianceGradient_continuousOn {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (varianceLogHeat c p.1 f) p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  obtain ⟨L,hL⟩ := varianceTilted_joint_bound hf hLip hf.deriv_bounded hc
  apply continuousOn_of_joint_bound (F := fun t => deriv (varianceLogHeat c t f)) (L := L)
  intro t ht s hs x y
  rw [deriv_varianceLogHeat_tilted hf hLip hc,deriv_varianceLogHeat_tilted hf hLip hc]
  exact hL t ht.1 s hs.1 x y

def gaussianRate (c : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2:ℝ)*deriv (deriv (varianceLogHeat c t f)) x+
    c/2*(deriv (varianceLogHeat c t f) x)^2

lemma gaussianRate_family {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    BoundedSmoothFamily (gaussianRate c f) := by
  have hu := varianceGradient_family hf hLip hc
  convert (hu.deriv.const_mul (1/2:ℝ)).add ((hu.mul hu).const_mul (c/2)) using 1
  funext t x
  simp only [gaussianRate,pow_two]

lemma gaussianRate_continuousOn {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => gaussianRate c f p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  have hu := varianceGradient_continuousOn hf hLip hc T
  have hv := (varianceGradient_family hf hLip hc).continuousOn_iteratedDeriv hu 1
  convert ((continuousOn_const (c := (1/2:ℝ))).mul hv).add
      ((continuousOn_const (c := c/2)).mul (hu.pow 2)) using 1
  funext p
  simp only [gaussianRate,iteratedDeriv_one,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]

lemma varianceLogHeat_integral_rate {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) :
    (∫ t in a..b, gaussianRate c f t x) = varianceLogHeat c b f x-varianceLogHeat c a f x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · intro t ht
    exact (varianceLogHeat_equation hf hLip c (ha.trans ht.1) x).continuousWithinAt.mono
      (fun s hs => ha.trans hs.1)
  · intro t ht
    exact (varianceLogHeat_equation hf hLip c (ha.trans ht.1.le) x).hasDerivAt
      (Ici_mem_nhds (ha.trans_lt ht.1))
  · exact (gaussianRate_family hf hLip hc).intervalIntegrable x a b

lemma gaussianRate_integral_derivative {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) (x : ℝ) :
    (∫ t in a..b, iteratedDeriv n (gaussianRate c f t) x) =
      iteratedDeriv n (varianceLogHeat c b f) x-iteratedDeriv n (varianceLogHeat c a f) x := by
  have he : (fun z => ∫ t in a..b, gaussianRate c f t z) =
      fun z => varianceLogHeat c b f z-varianceLogHeat c a f z :=
    funext (varianceLogHeat_integral_rate hf hLip hc ha hab)
  have hh := (gaussianRate_family hf hLip hc).iteratedDeriv_integral n a b x
  rw [he,iteratedDeriv_fun_sub (n := n)
    ((regularDatum_varianceLogHeat hf hLip hc b).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    ((regularDatum_varianceLogHeat hf hLip hc a).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)] at hh
  exact hh.symm

lemma hasDerivAt_varianceLogHeat_derivative {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun s => iteratedDeriv n (varianceLogHeat c s f) x)
      (iteratedDeriv n (gaussianRate c f t) x) t := by
  have hF := (gaussianRate_family hf hLip hc).iteratedDeriv n
  have hj := (gaussianRate_family hf hLip hc).continuousOn_iteratedDeriv
    (gaussianRate_continuousOn hf hLip hc (t+1)) n
  have hcont : ContinuousAt (fun s => iteratedDeriv n (gaussianRate c f s) x) t := by
    have hh := hj.comp (f := fun s : ℝ => (s,x)) (continuous_id.prodMk continuous_const).continuousOn
      (fun s (hs : s ∈ Icc (0:ℝ) (t+1)) => ⟨hs,mem_univ _⟩)
    exact (hh t ⟨ht.le,by linarith⟩).continuousAt (Icc_mem_nhds ht (by linarith))
  have hi := intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable x 0 t)
    ((hF.measurable.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.stronglyMeasurableAtFilter) hcont
  apply (hi.const_add (iteratedDeriv n (varianceLogHeat c 0 f) x)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [gaussianRate_integral_derivative hf hLip hc le_rfl hs.le n x]
  ring

end ZeroTemperatureSK.Heat

end
end

end OAI
