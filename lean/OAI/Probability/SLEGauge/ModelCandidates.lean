import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.AdaptedFailure

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart LoewnerGeometry CompactSequence MomentBatches

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

def candidateScale : ℝ := max 1 (400*subdiskReach (subdiskRadius M.radiusIndex)*
  subdiskDistortion (subdiskRadius M.radiusIndex))

def candidateLower : ℝ := (400*diskLower (subdiskRadius M.radiusIndex))^(2-alpha a)

lemma candidateScale_one : 1 ≤ M.candidateScale := le_max_left ..
lemma candidateScale_pos : 0 < M.candidateScale := zero_lt_one.trans_le M.candidateScale_one
lemma candidateLower_pos : 0 < M.candidateLower := by
  apply Real.rpow_pos_of_pos
  have := diskLower_pos (subdiskRadius M.radiusIndex)
  positivity

def spatialMass (b : GDriver) : Measure ℂ := spatialRestriction (M.mass ∞ b) univ

lemma spatialMass_apply (b : GDriver) (A : Set ℂ) (hA : MeasurableSet A) :
    M.spatialMass b A=M.mass ∞ b ((Subtype.val : UpperPlane→ℂ) ⁻¹' A) := by
  rw [spatialMass,spatialRestriction_apply _ _ _ hA,univ_inter]

lemma spatialMass_measurable (A : Set ℂ) (hA : MeasurableSet A) :
    Measurable (fun b=>M.spatialMass b A) :=
  spatialRestriction_measurable _ M.canonical.terminal_measurable _ MeasurableSet.univ _ hA

 
def candidate (n i : ℕ) (z : ℂ) (b : GDriver) : Prop :=
  ENNReal.ofReal (M.candidateLower*M.testThreshold n i*(batchRadius a (M.batchLevel n) n i)^(2-alpha a)) ≤
    M.spatialMass b (closedBall z (M.candidateScale*batchRadius a (M.batchLevel n) n i))

lemma candidate_measurable (n i : ℕ) (z : ℂ) : MeasurableSet {b | M.candidate n i z b} :=
  measurableSet_le measurable_const (M.spatialMass_measurable _ measurableSet_closedBall)

 

lemma success_implies_candidate (z : ℂ) (hz : 0<z.im) (n i : ℕ)
    (hy : 400*batchRadius a (M.batchLevel n) n i ≤ z.im) :
    ∀ᵐ b∂W,ENNReal.ofReal (M.testThreshold n i) ≤
      M.stoppedTest z (400*batchRadius a (M.batchLevel n) n i) (M.batchLevel n) b →
      M.candidate n i z b := by
  let r := batchRadius a (M.batchLevel n) n i
  let q := subdiskRadius M.radiusIndex
  have hr : 0<r := batchRadius_pos ..
  have hσ : 0<400*r := by positivity
  have hq : 0≤q := (subdiskRadius_pos _).le
  have hq1 : q<1 := subdiskRadius_lt_one _
  filter_upwards [M.canonical.path,actual_radial_spatial_bounds κ a ha W
    M.supports M.coeff M.nonneg M.canonical z hz (400*r) hσ hy q hq hq1] with b hb hbound
  intro hs
  have hT : radialTime a b.1 z (400*r*Real.exp (-2*a*M.batchLevel n))≠∞ := by
    intro he
    have hztest : M.stoppedTest z (400*r) (M.batchLevel n) b=0 := by
      simp only [stoppedTest,finiteStoppedTest,he,ite_eq_left]
    rw [hztest] at hs
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (M.testThreshold_pos n i))) hs
  have hS : radialTime a b.1 z (400*r)≠∞ := ne_top_of_le_ne_top hT
    (radialTime_antitone a (by linarith) z hz _ _
      (testEndpoint_pos (a:=a) _ hσ _) (testEndpoint_le (ha:=ha) _ hσ.le _) hy b)
  rw [M.stoppedTest_eq z hz (400*r) hσ hy _ b hT] at hs
  have hloc := (radialDiskRegion_localization a (by linarith) z hz (400*r) hσ hy
    (half_le_subdiskRadius M.radiusIndex) hq1 b hS).2
  have hl : radialDiskRegion a (by linarith) z (400*r) q b ⊆
      (Subtype.val : UpperPlane→ℂ) ⁻¹' closedBall z (M.candidateScale*r) := by
    refine hloc.trans (preimage_mono (closedBall_subset_closedBall ?_))
    have hA : 400*subdiskReach q*subdiskDistortion q ≤ M.candidateScale := le_max_right ..
    nlinarith [mul_le_mul_of_nonneg_right hA hr.le]
  have hmass := (mul_le_mul (le_refl
    (ENNReal.ofReal ((diskLower q*(400*r))^(2-alpha a)))) hs zero_le zero_le).trans ((hbound hS).2 (M.batchLevel n)).1
  have hmass' := hmass.trans (((hb.monotone le_top) _).trans (measure_mono hl))
  change ENNReal.ofReal (M.candidateLower*M.testThreshold n i*r^(2-alpha a)) ≤ _
  rw [M.spatialMass_apply _ _ measurableSet_closedBall]
  calc
    _ = ENNReal.ofReal ((diskLower q*(400*r))^(2-alpha a))*ENNReal.ofReal (M.testThreshold n i) := by
      rw [←ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (diskLower_pos q).le hσ.le) _)]
      congr 1
      rw [show diskLower q*(400*r)=(400*diskLower q)*r by ring,
        Real.mul_rpow (by have := diskLower_pos q; positivity) hr.le]
      dsimp [candidateLower,q]
      ring
    _ ≤ _ := hmass'

lemma batch_candidates (z : ℂ) (hz : 0<z.im) (n : ℕ)
    (hr : BatchReady a n) (hy : Real.exp (-(n:ℝ))≤z.im) :
    ∀ᵐ b∂W,(¬∃i<M.testCount n,M.candidate n i z b) → b∈M.batchFailures z n := by
  have hs : ∀ᵐ b∂W,∀i : ℕ, ENNReal.ofReal (M.testThreshold n i) ≤
      M.stoppedTest z (400*batchRadius a (M.batchLevel n) n i) (M.batchLevel n) b →
        M.candidate n i z b := ae_all_iff.mpr (fun i=>M.success_implies_candidate z hz n i
    ((batchBoundary_start a z.im (by linarith) hz _ _ hr hy i).1.trans
      (batchBoundary_le a z.im (by linarith) hz _ _ hr hy i)))
  filter_upwards [hs] with b hb hn i hi hsu
  exact hn ⟨i,hi,hb i hsu⟩

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry

lemma diskAt_norm_le_one {w v : ℂ} (hw : 0<w.im) (hv : 0<v.im) :
    ‖diskAt w v‖≤1 := by
  have hn : ‖v-w‖≤‖v-star w‖ := by
    rw [←sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im,sub_neg_eq_add]
    nlinarith [mul_pos hw hv]
  simpa only [diskAt,norm_div] using div_le_one_of_le₀ hn (norm_nonneg _)

 
theorem halfPlane_harnack_ball {f : ℂ→ℂ} {z v : ℂ} {r : ℝ} (hr : 0<r)
    (hf : DifferentiableOn ℂ f (ball z r))
    (hpos : ∀w∈ball z r,0<(f w).im) (hv : dist v z≤r/2) :
    (f v).im≤3*(f z).im := by
  have hz : z∈ball z r := mem_ball_self hr
  have hv' : v∈ball z r := lt_of_le_of_lt hv (by linarith)
  let g : ℂ→ℂ := fun w=>diskAt (f z) (f w)
  have hd : DifferentiableOn ℂ g (ball z r) := by
    intro w hw
    exact ((diskAt_hasDerivAt (hpos z hz) (hpos w hw)).differentiableAt.comp_differentiableWithinAt
      w (hf w hw))
  have hzero : g z=0 := by simp [g,diskAt]
  have hm : MapsTo g (ball z r) (closedBall (g z) 1) := by
    intro w hw
    simpa only [mem_closedBall,hzero,dist_zero_right] using diskAt_norm_le_one (hpos z hz) (hpos w hw)
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm hv'
  rw [hzero,dist_zero_right] at hs
  have hg : ‖g v‖≤1/2 := hs.trans (by
    calc
      _ ≤ (1/r)*(r/2) := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = _ := by field_simp)
  have hden : 0<‖f v-star (f z)‖ := norm_pos_iff.mpr (diskAt_denominator_ne (hpos z hz) (hpos v hv'))
  have hnum : ‖f v-f z‖≤(1/2)*‖f v-star (f z)‖ := by
    exact (div_le_iff₀ hden).mp (show ‖f v-f z‖/‖f v-star (f z)‖≤1/2 by
      simpa only [g,diskAt,norm_div] using hg)
  have hu : ‖f v-star (f z)‖≤‖f v-f z‖+2*(f z).im := by
    calc
      _ = ‖(f v-f z)+(f z-star (f z))‖ := by congr 1; ring
      _ ≤ ‖f v-f z‖+‖f z-star (f z)‖ := norm_add_le _ _
      _ = _ := by
        rw [show f z-star (f z)=((2*(f z).im:ℝ):ℂ)*Complex.I by
          apply Complex.ext <;> simp; ring,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (mul_pos (by norm_num) (hpos z hz)),Complex.norm_I,mul_one]
  have hi := Complex.im_le_norm (f v-f z)
  rw [Complex.sub_im] at hi
  linarith

end SLEExactGauge.LoewnerGeometry
end
end
 

 
section
 

noncomputable section
open Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry
open ExactSLEMain ExactSLEGreen LoewnerRestart FlowIdentification

 

theorem alive_of_height_floor (a : ℝ) {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} {ε : ℝ} (hε : 0<ε) (hz : ε≤z.im)
    (hfloor : ∀s≤T,alive a b s z → ε≤(loewnerMap a b s z).im) :
    alive a b T z := by
  have hη : 0<ε/2 := half_pos hε
  obtain ⟨F,hFc,hFe⟩ := exists_cutoff_loewner a (ε/2) hη b hb
  have hF0 : F 0 z=z := by simpa using hFe z 0
  let H : ℝ→ℝ := fun t=>(F t.toNNReal z).im
  have hc : Continuous H := Complex.continuous_im.comp ((hFc z).comp continuous_real_toNNReal)
  have he0 : H 0=z.im := by simp [H,hF0]
  have hode (s : ℝ≥0) (hs : ∀u∈Icc (0:ℝ) s,ε/2≤H u) :
      odeUntil a b z s (fun u=>F u.toNNReal z) := by
    refine ⟨by simpa using hF0,?_⟩
    intro u hu
    have hi := hs u hu
    refine ⟨hη.trans_le hi,?_⟩
    have hd := cutoff_loewner_hasDerivWithinAt hη hb hFc hFe z s u hu
    have hh : heightClamp (ε/2) (F u.toNNReal z-(b u.toNNReal:ℂ))=
        F u.toNNReal z-(b u.toNNReal:ℂ) := heightClamp_eq (by simpa [H] using hi)
    simpa only [cutoffVector,hh] using hd
  have hs : ∀u∈Icc (0:ℝ) T,ε/2≤H u := by
    by_contra! hn
    obtain ⟨u,hu,hlow⟩ := hn
    let S : Set ℝ := Icc 0 T ∩ {t | H t≤ε/2}
    have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_le hc continuous_const)
    obtain ⟨s,hs⟩ := hS.exists_isLeast ⟨u,hu,hlow.le⟩
    have hs0 : 0<s := by
      have hh := hs.1
      change s∈Icc 0 (T:ℝ) ∧ H s≤ε/2 at hh
      rcases hh.1.1.eq_or_lt with h|h
      · rw [←h,he0] at hh
        linarith [hh.2]
      · exact h
    have hpref : Ico 0 s ⊆ {t | ε/2≤H t} := by
      intro t ht
      change ε/2≤H t
      by_contra! ht'
      have hb : t∈S := ⟨⟨ht.1,ht.2.le.trans hs.1.1.2⟩,ht'.le⟩
      exact (not_le.mpr ht.2) (hs.2 hb)
    have hpref' : Icc 0 s ⊆ {t | ε/2≤H t} := by
      have hh := closure_minimal hpref (isClosed_le continuous_const hc)
      rwa [closure_Ico hs0.ne] at hh
    let s' : ℝ≥0 := ⟨s,hs0.le⟩
    have ho := hode s' (fun t ht=>hpref' ht)
    have hh := hfloor s' hs.1.1.2 ⟨_,ho⟩
    rw [loewnerMap_eq ho] at hh
    change ε≤H s at hh
    have hsH : H s≤ε/2 := hs.1.2
    linarith
  exact ⟨_,hode T hs⟩

 
lemma loewnerMap_height_antitone {a : ℝ} (ha : 0≤a) {b : ℝ≥0→ℝ}
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) {s t : ℝ≥0} (hs : s≤t) (ht : t≤T) :
    (loewnerMap a b t z).im≤(loewnerMap a b s z).im := by
  obtain ⟨f,hf⟩ := hT
  have hc := Complex.continuous_im.comp_continuousOn (odeUntil_continuousOn hf)
  have hd (u : ℝ) (hu : u∈Icc (0:ℝ) T) :
      HasDerivWithinAt (fun u=>(f u).im)
        (-a*(f u).im/Complex.normSq (f u-(b u.toNNReal:ℂ))) (Icc (0:ℝ) T) u := by
    have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt u (hf.2 u hu).2
    convert! hh using 1
    simp only [Complex.imCLM_apply,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,zero_div,zero_sub,Complex.sub_im,sub_zero]
    ring
  have hm : AntitoneOn (fun u=>(f u).im) (Icc (0:ℝ) T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (T:ℝ)) hc
      (fun u hu=>(hd u (interior_subset hu)).mono interior_subset)
      (fun u hu=>div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (hf.2 u (interior_subset hu)).1.le)
        (Complex.normSq_nonneg _))
  rw [loewnerMap_eq (odeUntil_mono hf ht),loewnerMap_eq (odeUntil_mono hf (hs.trans ht))]
  exact hm ⟨s.coe_nonneg,show (s:ℝ)≤T from hs.trans ht⟩ ⟨t.coe_nonneg,ht⟩ hs

 

theorem center_alive_of_ball_survival {a : ℝ} (ha : 0<a) (b : GDriver)
    {z v : ℂ} (hz : 0<z.im) {r : ℝ} (hr : 0<r) {T : ℝ≥0}
    (hball : ∀s≤T,alive a b.1 s z → ball z r ⊆ {w | alive a b.1 s w})
    (hv : dist v z≤r/2) (hT : alive a b.1 T v) : alive a b.1 T z := by
  let ε : ℝ := min z.im ((loewnerMap a b.1 T v).im/3)
  have hε : 0<ε := lt_min hz (div_pos (loewnerMap_im_pos hT) (by norm_num))
  apply alive_of_height_floor a b.1.continuous hε (min_le_left _ _)
  intro s hs hsz
  have hd : DifferentiableOn ℂ (loewnerMap a b.1 s) (ball z r) :=
    fun w hw=>(hasDerivAt_loewnerMap b.1.continuous (hball s hs hsz hw)).differentiableAt.differentiableWithinAt
  have hh := halfPlane_harnack_ball hr hd
    (fun w hw=>loewnerMap_im_pos (hball s hs hsz hw)) hv
  have hm := loewnerMap_height_antitone ha.le hT hs le_rfl
  exact (min_le_right z.im _).trans ((div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr (by linarith))

end SLEExactGauge.LoewnerGeometry
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry
open ExactSLEMain ExactSLEGreen LoewnerRestart FlowIdentification

 

theorem frontier_avoids_ball_of_no_crossing {a : ℝ} (ha : 0<a) (b : GDriver)
    {z : ℂ} (hz : 0<z.im) {r : ℝ} (hr : 0<r) (hy : 800*r≤z.im)
    (hno : radialTime a b.1 z (800*r)=∞) (T : ℝ≥0) :
    Disjoint (ball z (2*r)) (frontier {v | alive a b.1 T v}) := by
  have hball (s : ℝ≥0) (hs : alive a b.1 s z) :
      ball z (4*r) ⊆ {v | alive a b.1 s v} := by
    have hR := actual_radius_before_target a ha z hz (800*r)
      (by positivity) hy b s hs (by rw [hno]; exact le_top)
    exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans
      (radius_ball_subset_alive ha b s hs)
  by_cases hT : alive a b.1 T z
  · apply Set.disjoint_left.mpr
    intro v hv hf
    have hv' : v∈ball z (4*r) := ball_subset_ball (by linarith) hv
    rw [(isOpen_alive b.1.continuous T).frontier_eq] at hf
    exact hf.2 (hball T hT hv')
  · have hd : Disjoint (ball z (2*r)) {v | alive a b.1 T v} := by
      apply Set.disjoint_left.mpr
      intro v hv hvT
      apply hT
      apply center_alive_of_ball_survival ha b hz (by positivity : 0<4*r)
        (fun s _ hs=>hball s hs) _ hvT
      have hh := mem_ball.mp hv
      linarith
    apply Set.disjoint_left.mpr
    intro v hv hf
    have hc := frontier_subset_closure hf
    obtain ⟨w,hw,hws⟩ := mem_closure_iff_nhds.mp hc (ball z (2*r)) (isOpen_ball.mem_nhds hv)
    exact Set.disjoint_left.mp hd hw hws

 

theorem radial_crossing_of_frontier_visit {a : ℝ} (ha : 0<a) (b : GDriver)
    {z : ℂ} (hz : 0<z.im) {r : ℝ} (hr : 0<r) (hy : 800*r≤z.im)
    {v : ℂ} {T : ℝ≥0} (hv : v∈ball z (2*r))
    (hf : v∈frontier {w | alive a b.1 T w}) : radialTime a b.1 z (800*r)≠∞ := by
  intro hno
  exact Set.disjoint_left.mp (frontier_avoids_ball_of_no_crossing ha b hz hr hy hno T) hv hf

 

theorem trace_visit_probability_large {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W)
    {z : ℂ} (hz : 0<z.im) {r : ℝ} (hr : 0<r) (hy : 800*r≤z.im) :
    W {b | ∃t : ℝ, 0≤t ∧ Target.trace κ b t∈ball z (2*r)} ≤
      Jacobi.visitConstant (Target.a κ)*ENNReal.ofReal ((800*r/z.im)^(alpha (Target.a κ))) := by
  have hd := trace_regular_actual_domains hκ hκ8 hW
  have ha := TraceMassIntegration.a_gt_quarter hκ hκ8
  have hsub : {b : TDriver | ∃t : ℝ,0≤t ∧ Target.trace κ b t∈ball z (2*r)} ≤ᵐ[W]
      {b | radialTime (Target.a κ) (driverHomeomorph b).1 z (800*r)≠∞} := by
    filter_upwards [hd] with b hb hvisit
    obtain ⟨t,ht,hbt⟩ := hvisit
    exact radial_crossing_of_frontier_visit (by linarith) (driverHomeomorph b) hz hr hy hbt (hb.2.1 t ht)
  have hR := radialTime_stopping (Target.a κ) (by linarith) z hz (800*r) (by positivity) hy
  have hmeas : MeasurableSet {b : GDriver | radialTime (Target.a κ) b.1 z (800*r)≠∞} :=
    (hR.measurable' (measurableSet_singleton ∞)).compl
  calc
    _ ≤ W {b | radialTime (Target.a κ) (driverHomeomorph b).1 z (800*r)≠∞} := measure_mono_ae hsub
    _ = (W.map driverHomeomorph) {b | radialTime (Target.a κ) b.1 z (800*r)≠∞} :=
      (Measure.map_apply measurable_driverHomeomorph hmeas).symm
    _ ≤ _ := by
      let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
      let : IsProbabilityMeasure (W.map driverHomeomorph) := inferInstance
      exact Jacobi.radial_hit_probability_radius _ (brownian_map_driver W hW)
        _ ha z hz (800*r) (by positivity) hy

end SLEExactGauge.LoewnerGeometry
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology Classical
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart LoewnerGeometry CompactSequence MomentBatches

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

include ha in
lemma alpha_lt_one : alpha a<1 := by
  unfold alpha
  have ha0 : 0<a := by linarith
  have : 0<1/(4*a) := by positivity
  linarith

def cleanupEvent (z : ℂ) (n : ℕ) : Set GDriver :=
  if BatchReady a n ∧ Real.exp (-(n:ℝ)) ≤ z.im then
    M.batchFailures z n ∩ {b | radialTime a b.1 z (800*M.finalRadius n)≠∞}
  else if 800*M.finalRadius n≤z.im then
    {b | radialTime a b.1 z (800*M.finalRadius n)≠∞}
  else univ

lemma finalRadius_height (z : ℂ) (hz : 0<z.im) (n : ℕ)
    (hr : BatchReady a n) (hy : Real.exp (-(n:ℝ)) ≤ z.im) :
    800*M.finalRadius n ≤ z.im :=
  (batch_final_le a z.im (by linarith) hz _ _ _ (M.testCount_pos n hr.1) hr).trans
    (batchBoundary_le a z.im (by linarith) hz _ _ hr hy _)

lemma cleanupEvent_measurable (z : ℂ) (hz : 0<z.im) (n : ℕ) :
    MeasurableSet (M.cleanupEvent z n) := by
  have hh (hy : 800*M.finalRadius n≤z.im) :
      MeasurableSet {b : GDriver | radialTime a b.1 z (800*M.finalRadius n)≠∞} :=
    ((radialTime_stopping a (by linarith) z hz _
      (by have := M.finalRadius_pos n; positivity) hy).measurable' (measurableSet_singleton ∞)).compl
  unfold cleanupEvent
  split_ifs with h hy
  · exact (M.batch_failures_measurable z hz n h.1 h.2).inter (hh (M.finalRadius_height z hz n h.1 h.2))
  · exact hh hy
  · exact MeasurableSet.univ

def cellConstant (_ : CenteredMomentModel κ a ha W) : ℝ := max 1 (Jacobi.visitConstant a).toReal * (800:ℝ)^(alpha a)

lemma cellConstant_pos : 0<M.cellConstant :=
  mul_pos (zero_lt_one.trans_le (le_max_left ..)) (Real.rpow_pos_of_pos (by norm_num) _)

lemma cell_factor (r y : ℝ) (hr : 0<r) (hy : 0<y) :
    M.cellConstant*r^(alpha a)*y^(-alpha a) =
      max 1 (Jacobi.visitConstant a).toReal*((800*r/y)^(alpha a)) := by
  rw [Real.div_rpow (by positivity : 0≤800*r) hy.le,
    Real.mul_rpow (by norm_num : (0:ℝ)≤800) hr.le,
    div_eq_mul_inv,←Real.rpow_neg hy.le]
  unfold cellConstant
  ring

lemma cleanup_near [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : ℂ) (hz : 0<z.im) (n : ℕ) :
    W.real (M.cleanupEvent z n) ≤
      M.cellConstant*(M.finalRadius n)^(alpha a)*z.im^(-alpha a) := by
  have hrpos := M.finalRadius_pos n
  rw [M.cell_factor _ _ (M.finalRadius_pos n) hz]
  have hhit (hy : 800*M.finalRadius n≤z.im) :
      W.real {b | radialTime a b.1 z (800*M.finalRadius n)≠∞} ≤
        max 1 (Jacobi.visitConstant a).toReal*((800*M.finalRadius n/z.im)^(alpha a)) := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (Jacobi.visitConstant_lt_top a).ne ENNReal.ofReal_ne_top)
      (Jacobi.radial_hit_probability_radius W hW a ha z hz _
        (by have := M.finalRadius_pos n; positivity) hy)
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
  unfold cleanupEvent
  split_ifs with h hy
  · exact (measureReal_mono inter_subset_right).trans (hhit (M.finalRadius_height z hz n h.1 h.2))
  · exact hhit hy
  · change (W univ).toReal ≤ _
    rw [measure_univ, ENNReal.toReal_one]
    have hr : 1≤800*M.finalRadius n/z.im := (one_le_div hz).mpr (not_le.mp hy).le
    exact (mul_le_mul (le_max_left 1 _) (Real.one_le_rpow hr (alpha_pos ha).le) zero_le_one (zero_le_one.trans (le_max_left ..))) |>.trans' (by norm_num)

lemma cleanup_far [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : ℂ) (hz : 0<z.im) (n : ℕ) (hr : BatchReady a n)
    (hy : Real.exp (-(n:ℝ)) ≤ z.im) :
    W.real (M.cleanupEvent z n) ≤
      M.cellConstant*(M.finalRadius n)^(alpha a)*z.im^(-alpha a)*
        Real.exp (-((2:ℝ)^n/16)) := by
  have hrpos := M.finalRadius_pos n
  rw [cleanupEvent,ite_eq_left ⟨hr,hy⟩,M.cell_factor _ _ (M.finalRadius_pos n) hz]
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (Jacobi.visitConstant_lt_top a).ne ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
    (M.batch_failure_chordal hW z hz n hr hy)
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (Real.exp_pos _).le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)) (Real.exp_pos _).le)

 

lemma cleanup_covers (z : ℂ) (hz : 0<z.im) (n : ℕ) :
    ∀ᵐ b∂W,∀T : ℝ≥0,∀v∈closedBall z (M.finalRadius n),
      v∈frontier {w | alive a b.1 T w} →
      (∃i<M.testCount n,M.candidate n i z b) ∨ b∈M.cleanupEvent z n := by
  by_cases hh : BatchReady a n ∧ Real.exp (-(n:ℝ)) ≤ z.im
  · filter_upwards [M.batch_candidates z hz n hh.1 hh.2] with b hb T v hv hf
    by_cases hc : ∃i<M.testCount n,M.candidate n i z b
    · exact Or.inl hc
    · refine Or.inr ?_
      rw [cleanupEvent,ite_eq_left hh]
      refine ⟨hb hc,?_⟩
      exact radial_crossing_of_frontier_visit (by linarith) b hz (M.finalRadius_pos n)
        (M.finalRadius_height z hz n hh.1 hh.2)
        ((closedBall_subset_ball (by linarith [M.finalRadius_pos n])) hv) hf
  · apply Eventually.of_forall
    intro b T v hv hf
    right
    rw [cleanupEvent,ite_eq_right hh]
    split_ifs with hy
    · exact radial_crossing_of_frontier_visit (by linarith) b hz (M.finalRadius_pos n) hy
        ((closedBall_subset_ball (by linarith [M.finalRadius_pos n])) hv) hf
    · exact mem_univ b

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.CoverCost
open Deterministic

lemma hausdorff_le_liminf_bound {ι : ℕ→Type*} [∀n,Countable (ι n)]
    (h : ℝ→ℝ) (E : Set ℂ) (r : ℕ→ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (U : ∀n,ι n→Set ℂ) (C : ℕ→ℝ≥0∞)
    (hdiam : ∀ᶠ n in atTop,∀i,ediam (U n i) ≤ r n)
    (hcover : ∀ᶠ n in atTop,E ⊆ ⋃i,U n i)
    (hcost : ∀ᶠ n in atTop,(∑'i,diameterCost h (ediam (U n i))) ≤ C n) :
    Target.hausdorff h E ≤ liminf C atTop :=
  (hausdorff_le_liminf_cost h E r hr U hdiam hcover).trans (liminf_le_liminf hcost)

 

lemma hausdorff_le_liminf_of_exists {ι : ℕ→Type*} [∀n,Countable (ι n)]
    (h : ℝ→ℝ) (E : Set ℂ) (r : ℕ→ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (C : ℕ→ℝ≥0∞)
    (hcovers : ∀ᶠ n in atTop,∃U : ι n→Set ℂ,
      (∀i,ediam (U i)≤r n) ∧ E⊆⋃i,U i ∧
      (∑'i,diameterCost h (ediam (U i)))≤C n) :
    Target.hausdorff h E ≤ liminf C atTop := by
  classical
  let U : ∀n,ι n→Set ℂ := fun n=>Classical.epsilon (fun U : ι n→Set ℂ=>
    (∀i,ediam (U i)≤r n) ∧ E⊆⋃i,U i ∧
    (∑'i,diameterCost h (ediam (U i)))≤C n)
  have hU : ∀ᶠ n in atTop,(∀i,ediam (U n i)≤r n) ∧ E⊆⋃i,U n i ∧
      (∑'i,diameterCost h (ediam (U n i)))≤C n := by
    filter_upwards [hcovers] with n hn
    exact Classical.epsilon_spec hn
  exact hausdorff_le_liminf_bound h E r hr U C (hU.mono fun _ hn=>hn.1)
    (hU.mono fun _ hn=>hn.2.1) (hU.mono fun _ hn=>hn.2.2)

 

theorem liminf_cost_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : ℕ→Ω→ℝ≥0∞) (hC : ∀n,Measurable (C n)) (B : ℝ≥0∞)
    (hB : B<∞) (hbound : ∀ᶠ n in atTop,(∫⁻ω,C n ω∂P) ≤ B) :
    Measurable (fun ω=>liminf (fun n=>C n ω) atTop) ∧
    (∫⁻ω,liminf (fun n=>C n ω) atTop∂P) ≤ B ∧
    ∀ᵐ ω∂P,liminf (fun n=>C n ω) atTop<∞ := by
  have hmeas := Measurable.liminf hC
  have hI : (∫⁻ω,liminf (fun n=>C n ω) atTop∂P) ≤ B :=
    (lintegral_liminf_le hC).trans (liminf_le_of_frequently_le hbound.frequently)
  exact ⟨hmeas,hI,ae_lt_top hmeas (hI.trans_lt hB).ne⟩

 

theorem ae_hausdorff_finite_of_covers {Ω : Type*} [MeasurableSpace Ω]
    {ι : ℕ→Type*} [∀n,Countable (ι n)]
    (P : Measure Ω) (h : ℝ→ℝ) (E : Ω→Set ℂ)
    (r : ℕ→ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (U : ∀n,Ω→ι n→Set ℂ) (C : ℕ→Ω→ℝ≥0∞)
    (hC : ∀n,Measurable (C n)) (B : ℝ≥0∞) (hB : B<∞)
    (hbound : ∀ᶠ n in atTop,(∫⁻ω,C n ω∂P) ≤ B)
    (hdiam : ∀ᵐ ω∂P,∀ᶠ n in atTop,∀i,ediam (U n ω i) ≤ r n)
    (hcover : ∀ᵐ ω∂P,∀ᶠ n in atTop,E ω ⊆ ⋃i,U n ω i)
    (hcost : ∀ᵐ ω∂P,∀ᶠ n in atTop,(∑'i,diameterCost h (ediam (U n ω i))) ≤ C n ω) :
    (∀ᵐ ω∂P,Target.hausdorff h (E ω) ≤ liminf (fun n=>C n ω) atTop) ∧
    (∫⁻ω,liminf (fun n=>C n ω) atTop∂P) ≤ B ∧
    ∀ᵐ ω∂P,Target.hausdorff h (E ω)<∞ := by
  obtain ⟨hmeas,hI,hfin⟩ := liminf_cost_bound P C hC B hB hbound
  have hdom : ∀ᵐ ω∂P,Target.hausdorff h (E ω) ≤ liminf (fun n=>C n ω) atTop := by
    filter_upwards [hdiam,hcover,hcost] with ω hd hc hb
    exact hausdorff_le_liminf_bound h (E ω) r hr (fun n=>U n ω) (fun n=>C n ω) hd hc hb
  exact ⟨hdom,hI,by filter_upwards [hdom,hfin] with ω hd hf; exact hd.trans_lt hf⟩

end SLEExactGauge.CoverCost
end
end

end OAI
