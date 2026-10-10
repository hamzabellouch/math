import Mathlib
import OAI.Probability.SLELocalization.CommonClocks

namespace OAI


/-! Conformal localization and Driver Stability estimates. -/

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal unitInterval
namespace SLEExactGauge.DriverStability
open LoewnerCutoff

def timePath {T : ℝ} (hT : 0 ≤ T) (U : ℝ → ℝ) (hU : ContinuousOn U (Icc 0 T)) : C(I,ℝ) :=
  ⟨fun q => U (T*(q:ℝ)), hU.comp_continuous (continuous_const.mul continuous_subtype_val)
    (fun q => ⟨mul_nonneg hT q.property.1,by nlinarith [q.property.2]⟩)⟩

lemma extend_timePath {T : ℝ} (hT : 0 < T) (U : ℝ → ℝ) (hU : ContinuousOn U (Icc 0 T)) :
    EqOn (extendDriver T (timePath hT.le U hU)) U (Icc 0 T) := by
  intro t ht
  have hq : t/T ∈ Icc (0:ℝ) 1 := ⟨div_nonneg ht.1 hT.le,(div_le_one hT).2 ht.2⟩
  change U (T*(projIcc 0 1 zero_le_one (t/T):ℝ)) = U t
  rw [projIcc_of_mem _ hq]
  congr 1
  field_simp

lemma timePath_dist_le {T η : ℝ} (hT : 0 ≤ T) (hη : 0 ≤ η)
    (U V : ℝ → ℝ) (hU : ContinuousOn U (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ η) :
    dist (timePath hT U hU) (timePath hT V hV) ≤ η := by
  apply (ContinuousMap.dist_le hη).2
  intro q
  exact hUV _ ⟨mul_nonneg hT q.property.1,by nlinarith [q.property.2]⟩

lemma radius_of_positive_path
    {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing U γ g f) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε)
    (hU : ContinuousOn U (Icc 0 T)) (V : C(I,ℝ)) (z : ℂ)
    (hVU : EqOn (extendDriver T V) U (Icc 0 T))
    (hheight : ∀ t ∈ Icc 0 T, ε ≤ (position hε hT V z t).im) :
    z ∈ localizationDomain γ T ∧ LoewnerExit.radius hε hT V z T = loewnerRadius g T z := by
  have hh := h.cutoff_solution_live hε hT
    (H:=position hε hT V z)
    (fun t ht => by rw [← hVU ht]; exact position_derivWithin hε hT V z ht) hheight
  rw [position_initial] at hh
  have hl : logDerivative hε hT V z T = Real.log ‖deriv (g T) z‖ := by
    rw [logDerivative_eq_integral hε hT V z ⟨hT,le_rfl⟩,
      h.log_deriv_norm_eq hT hU hh.1]
    have hi := (h.continuous_spatialCoefficient hT hU hh.1).intervalIntegrable_of_Icc (μ:=MeasureTheory.volume) hT
    rw [← Complex.reCLM_apply,← Complex.reCLM.intervalIntegral_comp_comm hi]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    unfold variation
    rw [clampIm_eq (by simpa using hheight s hs)]
    simp only [← hh.2 hs,hVU hs,Complex.reCLM_apply]
  refine ⟨hh.1,?_⟩
  rw [LoewnerExit.radius,hl,Real.exp_log (norm_pos_iff.2 (h.deriv_ne_zero hT hh.1)),← hh.2 ⟨hT,le_rfl⟩]
  rfl

lemma live_radius_stable
    {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing U γ g f) {T ρ : ℝ} (hT : 0 < T)
    (hU : ContinuousOn U (Icc 0 T)) {z : ℂ} (hz : z ∈ localizationDomain γ T)
    (hρ : loewnerRadius g T z < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (V : ℝ → ℝ) (ξ : ℝ → ℂ) (G F : ℝ → ℂ → ℂ),
      IsLoewnerTraceUsing V ξ G F → ContinuousOn V (Icc 0 T) →
      (∀ t ∈ Icc 0 T, |V t-U t| < η) →
      z ∈ localizationDomain ξ T ∧ loewnerRadius G T z < ρ := by
  let ε : ℝ := (g T z).im/4
  have hε : 0 < ε := div_pos (h.im_pos hT.le hz) (by norm_num)
  let u : C(I,ℝ) := timePath hT.le U hU
  have heu : EqOn (extendDriver T u) U (Icc 0 T) := extend_timePath hT U hU
  have hbase : EqOn (fun t => g t z) (position hε hT.le u z) (Icc 0 T) :=
    h.eq_cutoff_solution hT.le hε hU hz (by dsimp [ε]; linarith [h.im_pos hT.le hz])
      (position_initial hε hT.le u z)
      (fun t ht => by rw [← heu ht]; exact position_derivWithin hε hT.le u z ht)
  have hbaseheight (t : ℝ) (ht : t ∈ Icc 0 T) : 4*ε ≤ (position hε hT.le u z t).im := by
    rw [← hbase ht]
    have hh := h.height_antitone hT.le hz ht ⟨hT.le,le_rfl⟩ ht.2
    dsimp [ε]
    linarith
  have hver : LoewnerExit.radius hε hT.le u z T = loewnerRadius g T z :=
    (radius_of_positive_path h hT.le hε hU u z heu (fun t ht => by linarith [hbaseheight t ht])).2
  have hp : ContinuousAt (fun v : C(I,ℝ) => solutionPath hε hT.le v z) u :=
    (solutionPath_lipschitz hε hT.le z).continuous.continuousAt
  have hr : ContinuousAt (fun v : C(I,ℝ) => LoewnerExit.radius hε hT.le v z T) u :=
    ((LoewnerExit.continuous_radius hε hT.le z).comp (continuous_id.prodMk continuous_const)).continuousAt
  have hn1 : ∀ᶠ v in 𝓝 u, dist (solutionPath hε hT.le v z) (solutionPath hε hT.le u z) < ε :=
    hp.eventually (ball_mem_nhds _ hε)
  have hn2 : ∀ᶠ v in 𝓝 u, LoewnerExit.radius hε hT.le v z T < ρ :=
    hr.eventually (gt_mem_nhds (by change LoewnerExit.radius hε hT.le u z T < ρ; rw [hver]; exact hρ))
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.1 (hn1.and hn2)
  refine ⟨δ/2,by positivity,fun V ξ G F hξ hV hclose => ?_⟩
  let v : C(I,ℝ) := timePath hT.le V hV
  have hev : EqOn (extendDriver T v) V (Icc 0 T) := extend_timePath hT V hV
  have hdist : dist v u < δ :=
    (timePath_dist_le hT.le (by positivity) V U hV hU (fun t ht => (hclose t ht).le)).trans_lt (by linarith)
  have hdv := hd hdist
  have hh (t : ℝ) (ht : t ∈ Icc 0 T) : ε ≤ (position hε hT.le v z t).im := by
    have hdiff : dist (position hε hT.le v z t) (position hε hT.le u z t) < ε := by
      rw [position_eq hε hT.le v z ht,position_eq hε hT.le u z ht]
      exact (ContinuousMap.dist_apply_le_dist (f:=solutionPath hε hT.le v z)
        (g:=solutionPath hε hT.le u z) (⟨t,ht⟩:Icc 0 T)).trans_lt hdv.1
    have him := Complex.abs_im_le_norm (position hε hT.le v z t-position hε hT.le u z t)
    rw [dist_eq_norm] at hdiff
    simp only [Complex.sub_im] at him
    have hlo := neg_abs_le ((position hε hT.le v z t).im-(position hε hT.le u z t).im)
    linarith [hbaseheight t ht]
  have hs := radius_of_positive_path hξ hT.le hε hV v z hev hh
  exact ⟨hs.1,hs.2 ▸ hdv.2⟩

end SLEExactGauge.DriverStability

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge

theorem uniformDriver_forces_tipVisit
    {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing U γ g f) {T r : ℝ} (hT : 0 < T)
    (hU : ContinuousOn U (Icc 0 T)) (hqr : 0 < (γ T).im) (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧ ∀ (V : ℝ → ℝ) (ξ : ℝ → ℂ) (G F : ℝ → ℂ → ℂ),
      IsLoewnerTraceUsing V ξ G F → ContinuousOn V (Icc 0 T) →
      (∀ t ∈ Icc 0 T, |V t-U t| < η) →
      ∃ t ∈ Icc 0 T, ξ t ∈ Metric.ball (γ T) r := by
  let q : ℂ := γ T
  let a : ℝ := min (r/4) (q.im/4)
  have ha : 0 < a := lt_min (by positivity) (by dsimp [q]; positivity)
  have har : a ≤ r/4 := min_le_left _ _
  have haq : a ≤ q.im/4 := min_le_right _ _
  let C : ℝ := 512*Real.pi
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := min (a/2) (a/(4*C))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have htip := h.2.2.2.2.2.2.2.2.2.2.2.2.2 T hT.le
  have hev : ∀ᶠ (y : ℝ) in 𝓝[>] (0:ℝ), dist (f T ((U T:ℂ)+(y:ℂ)*Complex.I)) q < δ :=
    htip.eventually (ball_mem_nhds _ hδ)
  obtain ⟨y,hy,hyδ⟩ := (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), 0 < y) hev).exists
  have hypos : 0 < y := hy
  let x : ℂ := f T ((U T:ℂ)+(y:ℂ)*Complex.I)
  have hx : x ∈ localizationDomain γ T :=
    h.2.2.2.2.2.2.2.2.1 T hT.le (by simpa [halfPlane] using hypos)
  have hxq : dist x q < δ := hyδ
  have hxsmall : dist x q < a/2 := hxq.trans_le (min_le_left _ _)
  have hnq : q ∉ localizationDomain γ T := by
    intro hq
    exact hq.1.2 ⟨T,⟨hT.le,le_rfl⟩,rfl⟩
  have hR : loewnerRadius g T x < a/2 := by
    calc
      _ ≤ C*dist x q := h.radius_le_complement_distance hT.le hx hnq
      _ < C*(a/(4*C)) := mul_lt_mul_of_pos_left (hxq.trans_le (min_le_right _ _)) hC
      _ = a/4 := by field_simp
      _ < a/2 := by linarith
  obtain ⟨η,hη,hstable⟩ := DriverStability.live_radius_stable h hT hU hx hR
  refine ⟨η,hη,fun V ξ G F hξ hV hclose => ?_⟩
  have hs := hstable V ξ G F hξ hV hclose
  by_contra hn
  push Not at hn
  have hfree : closedBall x a ⊆ halfPlane \ localizationSegment ξ 0 T := by
    intro w hw
    have hwx : dist w x ≤ a := hw
    have hwq : dist w q ≤ dist w x+dist x q := dist_triangle _ _ _
    have hwr : dist w q < r := by linarith
    have hwi : dist w q < q.im := by linarith
    have him := Complex.abs_im_le_norm (w-q)
    have hlo := neg_abs_le (w.im-q.im)
    rw [← dist_eq_norm] at him
    simp only [Complex.sub_im] at him
    refine ⟨by change 0 < w.im; linarith,?_⟩
    rintro ⟨t,ht,he⟩
    apply hn t ht
    change dist (ξ t) q < r
    simpa only [he] using hwr
  have hball := closedBall_subset_survivingDomain ha.le hs.1 hfree
  have hl := hξ.radius_ge_half_free_ball hT.le ha hs.1 hball
  exact (not_le_of_gt hs.2) hl

end SLEExactGauge

end

end

end OAI
