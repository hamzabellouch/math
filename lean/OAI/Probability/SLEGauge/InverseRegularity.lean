import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.InverseDomains

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.LiteralTrace
open Set Filter Metric MeasureTheory
open scoped Topology
theorem exists_inverseFlow (κ : ℝ) (hκ : 0 < κ) (b : Driver) {T : ℝ}
    (hT : 0 ≤ T) (w : ℂ) (hw : 0 < w.im) :
    ∃ z, Surviving κ b z T ∧ flow κ b z T = w := by
  let q : ℝ := w.im/2
  have hq : 0 < q := by dsimp [q]; positivity
  let br (t : ℝ) : ℝ := driverValue b (T-t)
  have hbr : Continuous br := (continuous_driverValue b).comp (continuous_const.sub continuous_id)
  obtain ⟨g,hg0,hgd⟩ := Cutoff.exists_solution_on_compact hq (-a κ) hbr w hT
  have hgc : ContinuousOn g (Icc 0 T) := fun t ht => (hgd t ht).continuousWithinAt
  let r (t : ℝ) : ℝ := a κ / Cutoff.denominator q (g t-br t)
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hr : ContinuousOn r (Icc 0 T) := by
    apply continuousOn_const.div
    · exact ((continuous_norm.comp_continuousOn
        (hgc.sub ((Complex.continuous_ofReal.comp hbr).continuousOn))).pow 2).sup continuousOn_const
    · intro t _
      exact (Cutoff.denominator_pos hq _).ne'
  have hyd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => (g u).im) (r t*(g t).im) (Icc 0 T) t := by
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (hgd t ht)
    convert! hi using 1
    simp only [Complex.imCLM_apply,Cutoff.field_im,neg_neg,r,div_mul_eq_mul_div]
  have hheight (t : ℝ) (ht : t ∈ Icc 0 T) : w.im ≤ (g t).im := by
    have hh := reverse_height_le hT (Complex.continuous_im.comp_continuousOn hgc) hr hyd
      (by simpa [hg0] using hw.le) (fun u _ => div_nonneg ha.le (Cutoff.denominator_pos hq _).le) t ht
    simpa [hg0] using hh
  have hrev (t : ℝ) (ht : t ∈ Icc 0 T) : T-t ∈ Icc 0 T := by
    constructor <;> linarith [ht.1,ht.2]
  let f (t : ℝ) : ℂ := g (T-t)
  have hf : PositiveSolution κ b (g T) T f := by
    refine ⟨hT,hgc.comp (continuous_const.sub continuous_id).continuousOn hrev,?_,?_,?_⟩
    · simp [f]
    · intro t ht
      exact hw.trans_le (hheight (T-t) (hrev t ht))
    · intro t ht
      have hcut := Cutoff.field_eq_div hq (-a κ) br (T-t) (g (T-t))
        ((by dsimp [q]; linarith : q ≤ w.im).trans (hheight (T-t) (hrev t ht)))
      have hd := (hgd (T-t) (hrev t ht)).scomp t
        (((hasDerivAt_const t T).sub (hasDerivAt_id t)).hasDerivWithinAt) hrev
      rw [hcut] at hd
      convert! hd using 1
      simp [f,br]
      ring
  refine ⟨g T,hf.surviving,?_⟩
  rw [hf.flow_eq]
  simpa [f] using hg0

lemma inverseFlow_surviving {κ : ℝ} (hκ : 0 < κ) (b : Driver) {T : ℝ} (hT : 0 ≤ T)
    {w : ℂ} (hw : 0 < w.im) : Surviving κ b (inverseFlow κ b T w) T :=
  (inverseFlow_spec (exists_inverseFlow κ hκ b hT w hw)).1

lemma flow_inverseFlow {κ : ℝ} (hκ : 0 < κ) (b : Driver) {T : ℝ} (hT : 0 ≤ T)
    {w : ℂ} (hw : 0 < w.im) : flow κ b (inverseFlow κ b T w) T = w :=
  (inverseFlow_spec (exists_inverseFlow κ hκ b hT w hw)).2
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace
open Set Filter Metric
open scoped NNReal Topology

lemma cutoffFlow_dist_le (κ : ℝ) (b : Driver) {j : ℕ} (hj : 1 ≤ j)
    (z w : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (cutoffFlow κ b j z t) (cutoffFlow κ b j w t) ≤
      dist z w * Real.exp ((|a κ| *3/((j:ℝ)^(-(2:ℤ)))^2)*T) := by
  have hd (x : ℂ) (u : ℝ) (hu : u ∈ Ico 0 T) :=
    ((cutoffFlow_solution κ b j hj x hT).2.2 u ⟨hu.1,hu.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hu.2) (Icc_subset_Icc_left hu.1))
  have hh := dist_le_of_trajectories_ODE (fun u => cutoffField_lipschitz κ b hj u)
    (cutoffFlow_continuous κ b hj z hT) (hd z)
    (cutoffFlow_continuous κ b hj w hT) (hd w)
    (show dist (cutoffFlow κ b j z 0) (cutoffFlow κ b j w 0) ≤ dist z w by
      rw [(cutoffFlow_solution κ b j hj z hT).2.1,(cutoffFlow_solution κ b j hj w hT).2.1]) t ht
  simp only [sub_zero] at hh
  change dist _ _ ≤ dist z w * Real.exp ((|a κ| *3/((j:ℝ)^(-(2:ℤ)))^2)*t) at hh
  have hK : 0 ≤ |a κ| *3/((j:ℝ)^(-(2:ℤ)))^2 := by positivity
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)) dist_nonneg)

lemma cutoffFlow_continuous_initial (κ : ℝ) (b : Driver) {j : ℕ} (hj : 1 ≤ j)
    {T : ℝ} (hT : 0 ≤ T) : Continuous (fun z => cutoffFlow κ b j z T) := by
  apply LipschitzWith.continuous (K := ⟨Real.exp ((|a κ| *3/((j:ℝ)^(-(2:ℤ)))^2)*T),by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change dist _ _ ≤ Real.exp ((|a κ| *3/((j:ℝ)^(-(2:ℤ)))^2)*T) * dist z w
  simpa only [mul_comm] using cutoffFlow_dist_le κ b hj z w hT ⟨hT,le_rfl⟩

 

lemma surviving_eventually_cutoff_height {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) :
    ∃ j : ℕ, 1 ≤ j ∧ ∀ᶠ w in 𝓝 z,
      Surviving κ b w T ∧ (∀ t ∈ Icc 0 T, flow κ b w t = cutoffFlow κ b j w t) ∧
      ∀ t ∈ Icc 0 T, (j:ℝ)⁻¹ < (flow κ b w t).im := by
  obtain ⟨j,hj,hgap⟩ := hz
  let m := sInf ((fun u : ℝ => (cutoffFlow κ b j z u).im) '' Icc 0 T)
  let C := Real.exp ((|a κ| *3/((j:ℝ)^(-(2:ℤ)))^2)*T)
  let ε := (m-(j:ℝ)⁻¹)/2
  have hε : 0 < ε := by dsimp [ε,m]; linarith
  have hC : 0 < C := Real.exp_pos _
  have hb := (isCompact_Icc.image_of_continuousOn
    (Complex.continuous_im.comp_continuousOn (cutoffFlow_continuous κ b hj z hT))).bddBelow
  refine ⟨j,hj,?_⟩
  filter_upwards [Metric.ball_mem_nhds z (div_pos hε hC)] with w hw
  have hd : dist z w*C < ε := by
    rw [← lt_div_iff₀ hC,dist_comm]
    exact hw
  have hg (t : ℝ) (ht : t ∈ Icc 0 T) : m-ε ≤ (cutoffFlow κ b j w t).im := by
    have h0 : m ≤ (cutoffFlow κ b j z t).im := csInf_le hb ⟨t,ht,rfl⟩
    have hh := cutoffFlow_dist_le κ b hj z w hT ht
    have hi : (cutoffFlow κ b j z t).im - (cutoffFlow κ b j w t).im ≤
        dist (cutoffFlow κ b j z t) (cutoffFlow κ b j w t) := by
      simpa only [dist_eq_norm,Complex.sub_im] using
        Complex.im_le_norm (cutoffFlow κ b j z t-cutoffFlow κ b j w t)
    change dist _ _ ≤ dist z w*C at hh
    linarith
  have hgapw : (j:ℝ)⁻¹ < sInf ((fun u : ℝ => (cutoffFlow κ b j w u).im) '' Icc 0 T) := by
    apply lt_of_lt_of_le (show (j:ℝ)⁻¹ < m-ε by dsimp [ε]; linarith)
    apply le_csInf (Set.Nonempty.image _ (show (Icc (0:ℝ) T).Nonempty from ⟨0,le_rfl,hT⟩))
    rintro y ⟨t,ht,rfl⟩
    exact hg t ht
  have hp := cutoff_positiveSolution hT hj hgapw
  refine ⟨hp.surviving,fun t ht => hp.flow_eqOn ht,?_⟩
  intro t ht
  rw [hp.flow_eqOn ht]
  exact lt_of_lt_of_le (show (j:ℝ)⁻¹ < m-ε by dsimp [ε]; linarith) (hg t ht)

lemma surviving_eventually_cutoff {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) :
    ∃ j : ℕ, 1 ≤ j ∧ ∀ᶠ w in 𝓝 z,
      Surviving κ b w T ∧ ∀ t ∈ Icc 0 T, flow κ b w t = cutoffFlow κ b j w t := by
  obtain ⟨j,hj,he⟩ := surviving_eventually_cutoff_height hT hz
  exact ⟨j,hj,he.mono fun w hw => ⟨hw.1,hw.2.1⟩⟩

lemma isOpen_surviving (κ : ℝ) (b : Driver) {T : ℝ} (hT : 0 ≤ T) :
    IsOpen {z | Surviving κ b z T} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨j,hj,he⟩ := surviving_eventually_cutoff hT hz
  exact he.mono fun w hw => hw.1

lemma flow_continuousAt_initial {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) : ContinuousAt (fun w => flow κ b w T) z := by
  obtain ⟨j,hj,he⟩ := surviving_eventually_cutoff hT hz
  apply (cutoffFlow_continuous_initial κ b hj hT).continuousAt.congr
  exact he.mono fun w hw => (hw.2 T ⟨hT,le_rfl⟩).symm
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace
open Set Filter Metric MeasureTheory
open scoped Topology

lemma complex_linear_formula {T : ℝ} {y r : ℝ → ℂ} (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (r t*y t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, y t = y 0 * Complex.exp (∫ u in (0:ℝ)..t, r (timeClip T u)) := by
  let A (t : ℝ) := ∫ u in (0:ℝ)..t, r (timeClip T u)
  have hc : Continuous (fun u => r (timeClip T u)) :=
    hr.comp_continuous (continuous_timeClip T) (timeClip_mem hT)
  have hA (t : ℝ) : HasDerivAt A (r (timeClip T t)) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hA' : Continuous A := continuous_iff_continuousAt.mpr fun t => (hA t).continuousAt
  have hd0 (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => y u * Complex.exp (-A u)) 0 (Icc 0 T) t := by
    have he := (hd t ht).mul ((hA t).neg.cexp.hasDerivWithinAt)
    rw [timeClip_eq ht] at he
    convert! he using 1
    ring
  have hconst := constant_of_has_deriv_right_zero
    (hy.mul ((Complex.continuous_exp.comp hA'.neg).continuousOn)) (fun t (ht : t ∈ Ico 0 T) =>
      (hd0 t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)))
  intro t ht
  have he := hconst t ht
  dsimp only [Pi.mul_apply,Function.comp_def,Pi.neg_apply] at he
  have hA0 : A 0 = 0 := by simp [A]
  rw [hA0,neg_zero,Complex.exp_zero,mul_one] at he
  calc
    y t = (y t * Complex.exp (-A t))*Complex.exp (A t) := by
      rw [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one]
    _ = y 0 * Complex.exp (A t) := by rw [he]

lemma surviving_centered_ne_zero {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    flow κ b z t-driverValue b t ≠ 0 := by
  have hi := (surviving_flow_positiveSolution hT hz).2.2.2.1 t ht
  intro he
  have := congrArg Complex.im he
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,sub_zero] at this
  linarith

 
lemma flow_difference_formula {κ : ℝ} {b : Driver} {z w : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) (hw : Surviving κ b w T) :
    flow κ b w T-flow κ b z T = (w-z)*Complex.exp
      (∫ u in (0:ℝ)..T, -(a κ:ℂ)/
        ((flow κ b z (timeClip T u)-driverValue b (timeClip T u))*
         (flow κ b w (timeClip T u)-driverValue b (timeClip T u)))) := by
  let f := flow κ b z
  let g := flow κ b w
  let r (u : ℝ) : ℂ := -(a κ:ℂ)/((f u-driverValue b u)*(g u-driverValue b u))
  have hf := surviving_flow_positiveSolution hT hz
  have hg := surviving_flow_positiveSolution hT hw
  have hcB : ContinuousOn (fun u => (driverValue b u:ℂ)) (Icc 0 T) :=
    (Complex.continuous_ofReal.comp (continuous_driverValue b)).continuousOn
  have hr : ContinuousOn r (Icc 0 T) :=
    continuousOn_const.div ((hf.2.1.sub hcB).mul (hg.2.1.sub hcB)) (fun t ht =>
      mul_ne_zero (surviving_centered_ne_zero hT hz ht) (surviving_centered_ne_zero hT hw ht))
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => g u-f u) (r t*(g t-f t)) (Icc 0 T) t := by
    have h := (hg.2.2.2.2 t ht).sub (hf.2.2.2.2 t ht)
    have hnz := surviving_centered_ne_zero hT hz ht
    have hnw := surviving_centered_ne_zero hT hw ht
    convert! h using 1
    dsimp [r,f,g]
    field_simp [hnz,hnw]
    ring
  have he := complex_linear_formula hT (hg.2.1.sub hf.2.1) hr hd T ⟨hT,le_rfl⟩
  have hf0 : f 0 = z := hf.2.2.1
  have hg0 : g 0 = w := hg.2.2.1
  simpa only [Pi.sub_apply,hf.2.2.1,hg.2.2.1] using he
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace
open Set Filter Metric MeasureTheory
open scoped Topology

lemma surviving_centered_continuous_clip {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) :
    Continuous (fun u => flow κ b z (timeClip T u)-driverValue b (timeClip T u)) :=
  ((surviving_flow_positiveSolution hT hz).2.1.comp_continuous (continuous_timeClip T)
    (timeClip_mem hT)).sub
    (Complex.continuous_ofReal.comp ((continuous_driverValue b).comp (continuous_timeClip T)))

def flowDifferenceExponent (κ : ℝ) (b : Driver) (z : ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..T, -(a κ:ℂ)/
    ((flow κ b z (timeClip T u)-driverValue b (timeClip T u))*
     (flow κ b w (timeClip T u)-driverValue b (timeClip T u)))

lemma flowDifferenceExponent_continuousAt {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) :
    ContinuousAt (flowDifferenceExponent κ b z T) z := by
  obtain ⟨j,hj,he⟩ := surviving_eventually_cutoff_height hT hz
  have hz' := he.self_of_nhds
  have hj0 : (0:ℝ) < j := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hq : 0 < (j:ℝ)⁻¹ := inv_pos.mpr hj0
  have hf := surviving_flow_positiveSolution hT hz
  have hzn (u : ℝ) : (j:ℝ)⁻¹ ≤
      ‖flow κ b z (timeClip T u)-driverValue b (timeClip T u)‖ := by
    exact (hz'.2.2 _ (timeClip_mem hT u)).le.trans
      (by simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using
        Complex.im_le_norm (flow κ b z (timeClip T u)-driverValue b (timeClip T u)))
  unfold flowDifferenceExponent
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => |a κ|/((j:ℝ)⁻¹*(j:ℝ)⁻¹))
  · filter_upwards [he] with w hw
    exact (continuous_const.div
      ((surviving_centered_continuous_clip hT hz).mul (surviving_centered_continuous_clip hT hw.1))
      (fun u => mul_ne_zero (surviving_centered_ne_zero hT hz (timeClip_mem hT u))
        (surviving_centered_ne_zero hT hw.1 (timeClip_mem hT u)))).aestronglyMeasurable
  · filter_upwards [he] with w hw
    apply Filter.Eventually.of_forall
    intro u _
    have hwn : (j:ℝ)⁻¹ ≤ ‖flow κ b w (timeClip T u)-driverValue b (timeClip T u)‖ := by
      exact (hw.2.2 _ (timeClip_mem hT u)).le.trans
        (by simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using
          Complex.im_le_norm (flow κ b w (timeClip T u)-driverValue b (timeClip T u)))
    rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,norm_mul]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hq hq)
      (mul_le_mul (hzn u) hwn hq.le (norm_nonneg _))
  · exact continuous_const.intervalIntegrable 0 T
  · apply Filter.Eventually.of_forall
    intro u _
    let t := timeClip T u
    have ht : t ∈ Icc 0 T := timeClip_mem hT u
    have hzt := (hf.restrict ht.1 ht.2).surviving
    apply continuousAt_const.div
      (continuousAt_const.mul ((flow_continuousAt_initial ht.1 hzt).sub continuousAt_const))
    exact mul_ne_zero (surviving_centered_ne_zero hT hz ht) (surviving_centered_ne_zero hT hz ht)

 

theorem flow_hasDerivAt_initial {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) :
    HasDerivAt (fun w => flow κ b w T)
      (Complex.exp (∫ u in (0:ℝ)..T, -(a κ:ℂ)/
        (flow κ b z (timeClip T u)-driverValue b (timeClip T u))^2)) z := by
  have hc := Complex.continuous_exp.continuousAt.comp (flowDifferenceExponent_continuousAt hT hz)
  have hh := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
  apply hasDerivAt_iff_tendsto_slope.mpr
  have he : ∀ᶠ w in 𝓝 z, Surviving κ b w T := (isOpen_surviving κ b hT).mem_nhds hz
  have heq : (fun w => Complex.exp (flowDifferenceExponent κ b z T w)) =ᶠ[𝓝[≠] z]
      slope (fun w => flow κ b w T) z := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hne
    have hn : w-z ≠ 0 := sub_ne_zero.mpr (by simpa using hne)
    rw [slope_def_field,flow_difference_formula hT hz hw]
    change _ = ((w-z)*Complex.exp (flowDifferenceExponent κ b z T w))/(w-z)
    field_simp
  simpa only [Function.comp_def,flowDifferenceExponent,pow_two] using hh.congr' heq

lemma flow_deriv_ne_zero {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) : deriv (fun w => flow κ b w T) z ≠ 0 := by
  rw [(flow_hasDerivAt_initial hT hz).deriv]
  exact Complex.exp_ne_zero _

lemma flow_differentiableOn (κ : ℝ) (b : Driver) {T : ℝ} (hT : 0 ≤ T) :
    DifferentiableOn ℂ (fun z => flow κ b z T) {z | Surviving κ b z T} := by
  intro z hz
  exact (flow_hasDerivAt_initial hT hz).differentiableAt.differentiableWithinAt
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace
open Set Filter Metric
open scoped Topology

lemma flow_hasStrictDerivAt_initial {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : Surviving κ b z T) :
    HasStrictDerivAt (fun w => flow κ b w T) (deriv (fun w => flow κ b w T) z) z :=
  ((flow_differentiableOn κ b hT).analyticAt ((isOpen_surviving κ b hT).mem_nhds hz)).hasStrictDerivAt

lemma inverseFlow_hasStrictDerivAt {κ : ℝ} (hκ : 0 < κ) (b : Driver) {T : ℝ}
    (hT : 0 ≤ T) {w : ℂ} (hw : 0 < w.im) :
    HasStrictDerivAt (inverseFlow κ b T)
      (deriv (fun z => flow κ b z T) (inverseFlow κ b T w))⁻¹ w := by
  have hz := inverseFlow_surviving hκ b hT hw
  have hf := flow_hasStrictDerivAt_initial hT hz
  have he : ∀ᶠ z in 𝓝 (inverseFlow κ b T w), inverseFlow κ b T (flow κ b z T) = z := by
    filter_upwards [(isOpen_surviving κ b hT).mem_nhds hz] with z hz'
    exact inverseFlow_flow hT hz'
  have hh := hf.to_local_left_inverse (flow_deriv_ne_zero hT hz) he
  rwa [flow_inverseFlow hκ b hT hw] at hh

 

theorem flow_conformal_bijection {κ : ℝ} (hκ : 0 < κ) (b : Driver) {T : ℝ} (hT : 0 ≤ T) :
    IsOpen {z | Surviving κ b z T} ∧
    BijOn (fun z => flow κ b z T) {z | Surviving κ b z T} {w | 0 < w.im} ∧
    DifferentiableOn ℂ (fun z => flow κ b z T) {z | Surviving κ b z T} ∧
    DifferentiableOn ℂ (inverseFlow κ b T) {w | 0 < w.im} := by
  refine ⟨isOpen_surviving κ b hT,⟨?_,flow_injOn κ b hT,?_⟩,
    flow_differentiableOn κ b hT,?_⟩
  · intro z hz
    exact (surviving_flow_positiveSolution hT hz).2.2.2.1 T ⟨hT,le_rfl⟩
  · intro w hw
    exact exists_inverseFlow κ hκ b hT w hw
  · intro w hw
    exact (inverseFlow_hasStrictDerivAt hκ b hT hw).hasDerivAt.differentiableAt.differentiableWithinAt
end SLEExactGauge.LiteralTrace

 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.BrownianCalculus

lemma integral_sq_gaussian (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hv
  simpa using hv

lemma integral_fourth_gaussian (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ)^2 := by
  let f : ℝ → ℝ := fun t => Real.exp ((v : ℝ) * t^2 / 2)
  have hf (t : ℝ) : HasDerivAt f ((v:ℝ) * t * f t) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul (v:ℝ)).div_const 2).exp using 1
    dsimp [f]
    ring
  have d0 : deriv f = fun t => (v:ℝ) * t * f t := funext fun t => (hf t).deriv
  have d1 : deriv (fun t => (v:ℝ) * t * f t) =
      fun t => ((v:ℝ) + (v:ℝ)^2*t^2) * f t := by
    ext t
    convert! (((hasDerivAt_id t).const_mul (v:ℝ)).mul (hf t)).deriv using 1
    dsimp
    ring
  have d2 : deriv (fun t => ((v:ℝ) + (v:ℝ)^2*t^2) * f t) =
      fun t => (3*(v:ℝ)^2*t + (v:ℝ)^3*t^3) * f t := by
    ext t
    convert! (((((hasDerivAt_id t).pow 2).const_mul ((v:ℝ)^2)).const_add (v:ℝ)).mul
      (hf t)).deriv using 1
    dsimp
    ring
  have d3 : deriv (fun t => (3*(v:ℝ)^2*t + (v:ℝ)^3*t^3) * f t) =
      fun t => (3*(v:ℝ)^2 + 6*(v:ℝ)^3*t^2 + (v:ℝ)^4*t^4) * f t := by
    ext t
    have hp := ((hasDerivAt_id t).const_mul (3*(v:ℝ)^2)).add
      (((hasDerivAt_id t).pow 3).const_mul ((v:ℝ)^3))
    convert! (hp.mul (hf t)).deriv using 1
    dsimp
    ring
  have hm := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) 4
  have he : mgf (fun x : ℝ => x) (gaussianReal 0 v) = f := by
    rw [mgf_fun_id_gaussianReal]
    simp only [zero_mul, zero_add, f]
  rw [he] at hm
  change iteratedDeriv 4 f 0 = (∫ x : ℝ, x^4 ∂gaussianReal 0 v) at hm
  rw [← hm]
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero, d0, d1, d2, d3, f]

open scoped ContinuousMapZero
abbrev Driver := C(ℝ≥0, ℝ)₀
instance : MeasurableSpace Driver := borel Driver
instance : BorelSpace Driver := ⟨rfl⟩

def increment (s h : ℝ≥0) (b : Driver) : ℝ := b (s+h) - b s

def history (s : ℝ≥0) (b : Driver) : Iic s → ℝ := fun t => b t

lemma measurable_increment (s h : ℝ≥0) : Measurable (increment s h) := by
  unfold increment
  exact (continuous_eval_const (s+h)).measurable.sub
    (continuous_eval_const s).measurable

lemma measurable_history (s : ℝ≥0) : Measurable (history s) := by
  exact Measurable.of_eval (fun time => (continuous_eval_const (time : ℝ≥0)).measurable)

variable {W : Measure Driver} (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
include hW

lemma increment_law (s h : ℝ≥0) : HasLaw (increment s h) (gaussianReal 0 h) W := by
  exact (hW.toIsPreBrownianReal.shift s).hasLaw_eval h

lemma increment_mean (s h : ℝ≥0) : (∫ b, increment s h b ∂W) = 0 := by
  rw [(increment_law hW s h).integral_eq, integral_id_gaussianReal]

lemma increment_sq (s h : ℝ≥0) : (∫ b, (increment s h b)^2 ∂W) = h := by
  exact ((increment_law hW s h).integral_comp (f := fun x : ℝ => x^2) (by fun_prop)).trans
    (integral_sq_gaussian h)

lemma increment_fourth (s h : ℝ≥0) :
    (∫ b, (increment s h b)^4 ∂W) = 3*(h:ℝ)^2 := by
  exact ((increment_law hW s h).integral_comp (f := fun x : ℝ => x^4) (by fun_prop)).trans
    (integral_fourth_gaussian h)

end SLEExactGauge.BrownianCalculus
end
end
end
end
end

end OAI
