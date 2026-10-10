import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.TraceBoundary

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
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
open Filter Topology
noncomputable section
open Complex Real Set Filter
open scoped Topology
noncomputable section
open scoped Topology
open MeasureTheory
noncomputable section
open Set Filter Real
open scoped Topology
open Set MeasureTheory ProbabilityTheory Topology Function Filter
open scoped NNReal ENNReal ContinuousMapZero
noncomputable section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
noncomputable section
open Set Filter Metric
open scoped Topology
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge.LiteralTrace
open TraceChaining
lemma PositiveSolution.initial_abs_re_le {κ : ℝ} {b : Driver} {z : ℂ} {T R : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) (hκ : 0 < κ) (hT : 0 ≤ T)
    (hB : ∀ u ∈ Icc 0 T, |driverValue b u| ≤ R) (hfT : |(f T).re| ≤ R) :
    |z.re| ≤ R := by
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hn (u : ℝ) (hu : u ∈ Icc 0 T) : 0 < ‖f u-driverValue b u‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (hf.shifted_ne_zero hu))
  apply abs_le.mpr
  constructor
  · have hh := initial_le_of_outward_deriv (R := R) hT
      (Complex.continuous_re.comp_continuousOn hf.2.1).neg
      (fun u hu => (hf.re_hasDeriv hu).neg) (by
        change -(f T).re ≤ R
        linarith [(abs_le.mp hfT).1])
      (by
        intro u hu hg
        change R < -(f u).re at hg
        have hBu := (abs_le.mp (hB u hu)).1
        have hm : 0 < -(a κ*((f u).re-driverValue b u)) := by nlinarith
        simpa only [neg_div] using div_pos hm (hn u hu))
    change -(f 0).re ≤ R at hh
    rw [hf.2.2.1] at hh
    linarith
  · have hh := initial_le_of_outward_deriv (R := R) hT
      (Complex.continuous_re.comp_continuousOn hf.2.1)
      (fun u hu => hf.re_hasDeriv hu) (abs_le.mp hfT).2
      (by
        intro u hu hg
        change R < (f u).re at hg
        have hBu := (abs_le.mp (hB u hu)).2
        exact div_pos (mul_pos ha (by linarith)) (hn u hu))
    change (f 0).re ≤ R at hh
    simpa only [hf.2.2.1] using hh

lemma inverseFlow_abs_re_le {κ T R y : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (hy : 0 < y) (b : Driver) (hB : ∀ u ∈ Icc 0 T, |driverValue b u| ≤ R) :
    |(radialValue κ b T y).re| ≤ R := by
  have hw : 0 < ((driverValue b T:ℂ)+y*Complex.I).im := by simpa using hy
  have hf := surviving_flow_positiveSolution hT (inverseFlow_surviving hκ b hT hw)
  apply hf.initial_abs_re_le hκ hT hB
  rw [flow_inverseFlow hκ b hT hw]
  simpa using hB T (right_mem_Icc.mpr hT)

lemma radial_limit_early_bound {κ T R : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (b : Driver)
    (hB : ∀ u ∈ Icc 0 T, |driverValue b u| ≤ R) {z : ℂ}
    (hz : Tendsto (radialValue κ b T) (𝓝[>] 0) (𝓝 z)) :
    ‖z‖ ≤ R+Real.sqrt (2*a κ*T) := by
  have hre : |z.re| ≤ R := by
    apply le_of_tendsto ((Complex.continuous_re.tendsto z).comp hz |>.abs)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact inverseFlow_abs_re_le hκ hT hy b hB
  have him0 : 0 ≤ z.im := by
    apply ge_of_tendsto ((Complex.continuous_im.tendsto z).comp hz)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (inverseFlow_im_pos hκ hT b (by simpa using hy)).le
  have hi : z.im^2 ≤ 2*a κ*T := by
    have hlim : Tendsto (fun y : ℝ => y^2+2*a κ*T) (𝓝[>] 0) (𝓝 (2*a κ*T)) := by
      simpa using (((tendsto_id'.mpr nhdsWithin_le_nhds :
        Tendsto (fun y : ℝ => y) (𝓝[>] (0:ℝ)) (𝓝 0)).pow 2).add_const (2*a κ*T))
    apply le_of_tendsto_of_tendsto (((Complex.continuous_im.tendsto z).comp hz).pow 2) hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using inverseFlow_im_sq_bound hκ hT b
      (show 0 < ((driverValue b T:ℂ)+y*Complex.I).im by simpa using hy)
  have hi' : z.im ≤ Real.sqrt (2*a κ*T) := (Real.le_sqrt him0 (by exact mul_nonneg (mul_nonneg (by norm_num) (div_pos (by norm_num) hκ).le) hT)).mpr hi
  calc
    ‖z‖ ≤ |z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ R+Real.sqrt (2*a κ*T) := by rw [abs_of_nonneg him0]; linarith
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open Set Filter Topology

lemma inverseFlow_zero (κ : ℝ) (hκ : 0 < κ) (b : Driver) {w : ℂ} (hw : 0 < w.im) :
    inverseFlow κ b 0 w = w := by
  have hs := inverseFlow_surviving hκ b (le_refl 0) hw
  have hf := surviving_flow_positiveSolution (le_refl 0) hs
  have he := flow_inverseFlow hκ b (le_refl 0) hw
  rwa [hf.2.2.1] at he

 

lemma trace_zero (κ : ℝ) (hκ : 0 < κ) (b : Driver) : trace κ b 0 = 0 := by
  unfold trace
  simp only [mul_zero,driverValue,Real.toNNReal_zero,map_zero,Complex.ofReal_zero,zero_add]
  apply Filter.Tendsto.limUnder_eq
  have hc : Tendsto (fun ε : ℝ => (ε:ℂ)*Complex.I) (nhdsWithin 0 (Ioi 0)) (𝓝 (0:ℂ)) := by
    have hc0 : Continuous (fun ε : ℝ => (ε:ℂ)*Complex.I) :=
      Complex.continuous_ofReal.mul continuous_const
    have h : Tendsto (fun ε : ℝ => (ε:ℂ)*Complex.I)
        (nhdsWithin 0 (Ioi 0)) (𝓝 ((0:ℂ)*Complex.I)) :=
      (hc0.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (inverseFlow_zero κ hκ b (by simpa using hε)).symm
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace

lemma trace_limit_zero {κ : ℝ} (hκ : 0 < κ) (b : Driver) :
    Tendsto (fun y : ℝ => inverseFlow κ b (κ*0)
      (driverValue b (κ*0)+y*Complex.I)) (𝓝[>] 0) (𝓝 (trace κ b 0)) := by
  rw [trace_zero κ hκ b]
  simp only [mul_zero,driverValue,Real.toNNReal_zero,map_zero,Complex.ofReal_zero,zero_add]
  have hc : Tendsto (fun y : ℝ => (y:ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    simpa only [Complex.ofReal_zero,zero_mul] using
      ((Complex.continuous_ofReal.tendsto 0).mul_const Complex.I).mono_left nhdsWithin_le_nhds
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (inverseFlow_zero κ hκ b (by simpa using hy)).symm

lemma trace_continuousWithinAt_zero {κ : ℝ} (hκ : 0 < κ) (b : Driver)
    (hlim : ∀ t : ℝ, 0 < t → Tendsto (fun y : ℝ => inverseFlow κ b (κ*t)
        (driverValue b (κ*t)+y*Complex.I)) (𝓝[>] 0) (𝓝 (trace κ b t))) :
    ContinuousWithinAt (trace κ b) (Ici 0) 0 := by
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hB : Continuous (driverValue b) := (map_continuous b).comp continuous_real_toNNReal
  have hB0 : driverValue b 0 = 0 := by simp [driverValue]
  have hz := trace_zero κ hκ b
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hδB⟩ := Metric.continuousAt_iff.mp (hB.continuousAt (x := 0))
    (ε/2) (by linarith)
  have hi : 0 < ε^2/(8*a κ*κ) := by positivity
  refine ⟨min (δ/κ) (ε^2/(8*a κ*κ)),lt_min (div_pos hδ hκ) hi,?_⟩
  intro t ht htd
  have ht0 : 0 ≤ t := ht
  have hts : t < min (δ/κ) (ε^2/(8*a κ*κ)) := by
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ht0] using htd
  rcases ht0.eq_or_lt with he | hp
  · subst t
    simp only [dist_self]
    exact hε
  have htδ : κ*t < δ := by
    have hh := (lt_div_iff₀ hκ).mp (hts.trans_le (min_le_left _ _))
    nlinarith
  have hdr (u : ℝ) (hu : u ∈ Icc 0 (κ*t)) : |driverValue b u| ≤ ε/2 := by
    have hh := hδB (show dist u (0:ℝ) < δ from by
      rw [Real.dist_eq,sub_zero,abs_of_nonneg hu.1]
      exact hu.2.trans_lt htδ)
    simpa only [Real.dist_eq,hB0,sub_zero] using hh.le
  have hbnd := radial_limit_early_bound hκ (mul_nonneg hκ.le ht0) b hdr (hlim t hp)
  have hroot : Real.sqrt (2*a κ*(κ*t)) < ε/2 := by
    apply (Real.sqrt_lt (by positivity) (by linarith : 0 ≤ ε/2)).mpr
    have hh := (lt_div_iff₀ (by positivity : 0 < 8*a κ*κ)).mp
      (hts.trans_le (min_le_right _ _))
    nlinarith
  rw [hz,dist_zero_right]
  linarith
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open MeasureTheory

lemma surviving_of_le {κ : ℝ} {b : Driver} {z : ℂ} {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hz : Surviving κ b z t) : Surviving κ b z s :=
  ((surviving_flow_positiveSolution (hs.trans hst) hz).restrict hs hst).surviving

lemma radial_limit_mem_closure {κ T s : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s) (hsT : s ≤ T)
    (b : Driver) {z : ℂ}
    (hz : Tendsto (fun y : ℝ => inverseFlow κ b T (driverValue b T+y*Complex.I))
      (𝓝[>] 0) (𝓝 z)) : z ∈ closure {w | Surviving κ b w s} := by
  apply mem_closure_of_tendsto hz
  filter_upwards [self_mem_nhdsWithin] with y hy
  apply surviving_of_le hs hsT
  exact inverseFlow_surviving hκ b (hs.trans hsT) (by simpa using hy)

lemma radial_limit_not_surviving {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (b : Driver)
    {z : ℂ} (hz : Tendsto (fun y : ℝ => inverseFlow κ b T (driverValue b T+y*Complex.I))
      (𝓝[>] 0) (𝓝 z)) : ¬ Surviving κ b z T := by
  intro hs
  have hg := (flow_continuousAt_initial hT hs).tendsto.comp hz
  have he : (fun y : ℝ => flow κ b (inverseFlow κ b T (driverValue b T+y*Complex.I)) T) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => (driverValue b T:ℂ)+y*Complex.I) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact flow_inverseFlow hκ b hT (by simpa using hy)
  have hl : Tendsto (fun y : ℝ => (driverValue b T:ℂ)+y*Complex.I)
      (𝓝[>] 0) (𝓝 (driverValue b T:ℂ)) := by
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using
      (((Complex.continuous_ofReal.tendsto 0).mul_const Complex.I).const_add (driverValue b T:ℂ)).mono_left
        nhdsWithin_le_nhds
  have hid : flow κ b z T = driverValue b T := tendsto_nhds_unique (hg.congr' he) hl
  have hpos := (surviving_flow_positiveSolution hT hs).2.2.2.1 T ⟨hT,le_rfl⟩
  rw [hid,Complex.ofReal_im] at hpos
  exact (lt_irrefl 0) hpos

lemma radial_limit_mem_frontier {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (b : Driver)
    {z : ℂ} (hz : Tendsto (fun y : ℝ => inverseFlow κ b T (driverValue b T+y*Complex.I))
      (𝓝[>] 0) (𝓝 z)) : z ∈ frontier {w | Surviving κ b w T} := by
  rw [(isOpen_surviving κ b hT).frontier_eq]
  exact ⟨radial_limit_mem_closure hκ hT le_rfl b hz,radial_limit_not_surviving hκ hT b hz⟩

 

theorem trace_countable_boundary {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {W : WienerLaw} (hW : IsWiener W) (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) :
    ∀ᵐ b ∂W, ∀ n : ℕ,
      trace κ b (t n) ∈ frontier {z | Surviving κ b z (κ*t n)} ∧
        ∀ s : ℝ, 0 ≤ s → s ≤ t n →
          trace κ b (t n) ∈ closure {z | Surviving κ b z (κ*s)} := by
  filter_upwards [trace_limit_countable hκ hκ8 hW t ht] with b hb
  intro n
  refine ⟨radial_limit_mem_frontier hκ (mul_nonneg hκ.le (ht n)) b (hb n),?_⟩
  intro s hs hst
  exact radial_limit_mem_closure hκ (mul_nonneg hκ.le hs)
    (mul_le_mul_of_nonneg_left hst hκ.le) b (hb n)
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open Set Filter Topology MeasureTheory

 

theorem trace_regular_all_times {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {W : WienerLaw} (hW : IsWiener W) :
    ∀ᵐ b ∂W,
      (∀ t : ℝ, 0 ≤ t →
        Tendsto (fun y : ℝ => inverseFlow κ b (κ*t)
          (driverValue b (κ*t)+y*Complex.I)) (𝓝[>] 0) (𝓝 (trace κ b t))) ∧
      ContinuousOn (trace κ b) (Ici 0) ∧
      (∀ t : ℝ, 0 ≤ t → trace κ b t ∈ frontier {z | Surviving κ b z (κ*t)}) ∧
      (∀ s : ℝ, 0 ≤ s →
        (trace κ b) '' Ici s ⊆ closure {z | Surviving κ b z (κ*s)}) := by
  filter_upwards [trace_limit_all_positive hκ hκ8 hW,
    trace_continuous_positive hκ hκ8 hW] with b hlim hc
  have hall (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun y : ℝ => inverseFlow κ b (κ*t)
        (driverValue b (κ*t)+y*Complex.I)) (𝓝[>] 0) (𝓝 (trace κ b t)) := by
    rcases ht.eq_or_lt with he | hp
    · subst t
      exact trace_limit_zero hκ b
    · exact hlim t hp
  refine ⟨hall,?_,?_,?_⟩
  · intro t ht
    rcases (show 0 ≤ t from ht).eq_or_lt with he | hp
    · subst t
      exact trace_continuousWithinAt_zero hκ b hlim
    · exact (hc.continuousAt (isOpen_Ioi.mem_nhds hp)).continuousWithinAt
  · intro t ht
    exact radial_limit_mem_frontier hκ (mul_nonneg hκ.le ht) b (hall t ht)
  · intro s hs z hz
    obtain ⟨t,ht,rfl⟩ := hz
    exact radial_limit_mem_closure hκ (mul_nonneg hκ.le hs)
      (mul_le_mul_of_nonneg_left ht hκ.le) b (hall t (hs.trans ht))

end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open Set Filter Topology MeasureTheory

 
def unboundedHalfPlaneComponent (K : Set ℂ) : Set ℂ :=
  {z | z ∈ {w : ℂ | 0 < w.im} \ K ∧
    ¬ Bornology.IsBounded (connectedComponentIn ({w : ℂ | 0 < w.im} \ K) z)}

lemma inverseFlow_image_upper {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (b : Driver) :
    inverseFlow κ b T '' {w : ℂ | 0 < w.im} = {z : ℂ | Surviving κ b z T} := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact inverseFlow_surviving hκ b hT hw
  · intro hz
    refine ⟨flow κ b z T,?_,inverseFlow_flow hT hz⟩
    exact (surviving_flow_positiveSolution hT hz).2.2.2.1 T ⟨hT,le_rfl⟩

lemma isPreconnected_surviving {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (b : Driver) :
    IsPreconnected {z : ℂ | Surviving κ b z T} := by
  rw [← inverseFlow_image_upper hκ hT b]
  exact (convex_halfSpace_im_gt 0).isPreconnected.image _
    (fun w hw => (inverseFlow_hasStrictDerivAt hκ b hT hw).hasDerivAt.continuousAt.continuousWithinAt)

lemma not_isBounded_surviving {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (b : Driver) :
    ¬ Bornology.IsBounded {z : ℂ | Surviving κ b z T} := by
  intro hb
  obtain ⟨R,hR,hb⟩ := hb.exists_pos_norm_le
  let w : ℂ := (R+1)*Complex.I
  have hw : 0 < w.im := by dsimp [w]; simpa using (show 0 < R+1 by linarith)
  have hz := inverseFlow_surviving hκ b hT hw
  have hf := surviving_flow_positiveSolution hT hz
  have hi := hf.im_antitone hκ (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
  dsimp only at hi
  rw [hf.2.2.1,flow_inverseFlow hκ b hT hw] at hi
  have hn := (Complex.im_le_norm (inverseFlow κ b T w)).trans (hb _ hz)
  have he : w.im = R+1 := by simp [w]
  rw [he] at hi
  linarith

 

theorem surviving_subset_trace_component {κ : ℝ} (hκ : 0 < κ) (b : Driver)
    (hlim : ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun y : ℝ => inverseFlow κ b (κ*t)
        (driverValue b (κ*t)+y*Complex.I)) (𝓝[>] 0) (𝓝 (trace κ b t)))
    {t : ℝ} (ht : 0 ≤ t) :
    {z : ℂ | Surviving κ b z (κ*t)} ⊆
      unboundedHalfPlaneComponent ((trace κ b) '' Icc 0 t) := by
  have hT : 0 ≤ κ*t := mul_nonneg hκ.le ht
  have hsub : {z : ℂ | Surviving κ b z (κ*t)} ⊆
      {w : ℂ | 0 < w.im} \ ((trace κ b) '' Icc 0 t) := by
    intro z hz
    refine ⟨?_,?_⟩
    · have hh := (surviving_flow_positiveSolution hT hz).2.2.2.1 0
        (left_mem_Icc.mpr hT)
      rwa [(surviving_flow_positiveSolution hT hz).2.2.1] at hh
    · rintro ⟨s,hs,rfl⟩
      exact radial_limit_not_surviving hκ (mul_nonneg hκ.le hs.1) b (hlim s hs.1)
        (surviving_of_le (mul_nonneg hκ.le hs.1)
          (mul_le_mul_of_nonneg_left hs.2 hκ.le) hz)
  intro z hz
  refine ⟨hsub hz,?_⟩
  intro hb
  exact not_isBounded_surviving hκ hT b (hb.subset
    ((isPreconnected_surviving hκ hT b).subset_connectedComponentIn hz hsub))

end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open Set Filter Topology MeasureTheory

 

theorem trace_generation_partial {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {W : WienerLaw} (hW : IsWiener W) :
    ∀ᵐ b ∂W,
      (∀ t : ℝ, 0 ≤ t →
        Tendsto (fun ε : ℝ => inverseFlow κ b (κ*t)
          (driverValue b (κ*t)+ε*Complex.I)) (𝓝[>] 0) (𝓝 (trace κ b t))) ∧
      ContinuousOn (trace κ b) (Ici 0) ∧
      (∀ t : ℝ, 0 ≤ t →
        {z : ℂ | Surviving κ b z (κ*t)} ⊆
          unboundedHalfPlaneComponent ((trace κ b) '' Icc 0 t)) ∧
      (∀ t : ℝ, 0 ≤ t →
        (trace κ b) '' Ici t ⊆ closure {z : ℂ | Surviving κ b z (κ*t)}) := by
  filter_upwards [trace_regular_all_times hκ hκ8 hW] with b hb
  exact ⟨hb.1,hb.2.1,fun t ht => surviving_subset_trace_component hκ b hb.1 ht,
    hb.2.2.2⟩

 

def MissingReverseTraceDomainObligation : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 → ∀ W : WienerLaw, IsWiener W →
    ∀ᵐ b ∂W, ∀ t : ℝ, 0 ≤ t →
      unboundedHalfPlaneComponent ((trace κ b) '' Icc 0 t) ⊆
        {z : ℂ | Surviving κ b z (κ*t)}

end SLEExactGauge.LiteralTrace
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
