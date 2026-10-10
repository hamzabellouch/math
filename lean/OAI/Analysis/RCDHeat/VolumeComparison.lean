import Mathlib
import OAI.Analysis.RCDHeat.DynamicalPlan

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: VolumeComparison, VolumeComparison, RatioComparison, VolumeComparison, VolumeComparison, VolumeComparison. -/



namespace RegularPointCoordinates

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
section SinMulDivSinGe
open scoped ENNReal
open Set

 
theorem sin_mul_div_sin_ge {a t : ℝ} (ha0 : 0 < a) (haπ : a < Real.pi)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ Real.sin (t*a) / Real.sin a := by
  have hh := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0:ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show a ∈ Icc 0 Real.pi from ⟨ha0.le,haπ.le⟩)
    (sub_nonneg.mpr ht1) ht0 (show 1-t+t = 1 by ring)
  apply (le_div_iff₀ (Real.sin_pos_of_pos_of_lt_pi ha0 haπ)).mpr
  simpa only [smul_eq_mul, mul_zero, Real.sin_zero, zero_add] using hh

 theorem sinh_le_mul_exp {a : ℝ} (_ha : 0 ≤ a) : Real.sinh a ≤ a*Real.exp a := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-2*a)) (Real.exp_pos a).le
  have he : Real.exp a * Real.exp (-2*a) = Real.exp (-a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hh
  rw [Real.sinh_eq]
  nlinarith

 theorem sinh_mul_div_sinh_ge {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t / Real.exp a ≤ Real.sinh (t*a) / Real.sinh a := by
  have hs : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  apply (div_le_div_iff₀ (Real.exp_pos a) hs).mpr
  have hh := sinh_le_mul_exp ha.le
  have hm := Real.self_le_sinh_iff.mpr (mul_nonneg ht ha.le)
  calc
    t*Real.sinh a ≤ t*(a*Real.exp a) := mul_le_mul_of_nonneg_left hh ht
    _ = (t*a)*Real.exp a := by ring
    _ ≤ Real.sinh (t*a)*Real.exp a := mul_le_mul_of_nonneg_right hm (Real.exp_pos a).le

 

noncomputable def distortionFloor (K N D t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (t / Real.exp (D*Real.sqrt (|K|/(N-1))))

 theorem distortionFloor_le_time (K N D t : ℝ) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    distortionFloor K N D t ≤ ENNReal.ofReal t := by
  apply ENNReal.ofReal_le_ofReal
  apply div_le_self ht
  exact Real.one_le_exp_iff.mpr (mul_nonneg hD (Real.sqrt_nonneg _))

 theorem distortionFloor_le_sigma (K N D θ t : ℝ) (hN : 1 < N)
    (hθ : 0 ≤ θ) (hθD : θ ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    distortionFloor K N D t ≤ sigma K N t θ := by
  have hD := hθ.trans hθD
  have hNm : 0 < N-1 := sub_pos.mpr hN
  unfold sigma
  split_ifs with hz hconj hK
  · exact distortionFloor_le_time K N D t hD ht0
  · exact le_top
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm (not_or.mp hz).1)
    have hroot : 0 < Real.sqrt (K/(N-1)) := Real.sqrt_pos.mpr (div_pos hK hNm)
    have ha0 : 0 < θ*Real.sqrt (K/(N-1)) := mul_pos hθpos hroot
    have hasq : (θ*Real.sqrt (K/(N-1)))^2 = K*θ^2/(N-1) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hK.le hNm.le)]
      ring
    have hasq_lt : (θ*Real.sqrt (K/(N-1)))^2 < Real.pi^2 := by
      rw [hasq, div_lt_iff₀ hNm]
      nlinarith [lt_of_not_ge hconj]
    have haπ : θ*Real.sqrt (K/(N-1)) < Real.pi := by nlinarith [Real.pi_pos]
    refine (distortionFloor_le_time K N D t hD ht0).trans (ENNReal.ofReal_le_ofReal ?_)
    simpa only [mul_assoc] using sin_mul_div_sin_ge ha0 haπ ht0 ht1
  · have hKneg : K < 0 := lt_of_le_of_ne (le_of_not_gt hK) (not_or.mp hz).2
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm (not_or.mp hz).1)
    have hroot : 0 < Real.sqrt (-K/(N-1)) := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) hNm)
    unfold distortionFloor
    rw [abs_of_neg hKneg]
    apply ENNReal.ofReal_le_ofReal
    calc
      t/Real.exp (D*Real.sqrt (-K/(N-1))) ≤ t/Real.exp (θ*Real.sqrt (-K/(N-1))) := by
        exact div_le_div_of_nonneg_left ht0 (Real.exp_pos _)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθD hroot.le))
      _ ≤ _ := by simpa only [mul_assoc] using sinh_mul_div_sinh_ge (mul_pos hθpos hroot) ht0

 theorem distortionFloor_le_tau (K N D θ t : ℝ) (hN : 1 < N)
    (hθ : 0 ≤ θ) (hθD : θ ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    distortionFloor K N D t ≤ tau K N t θ := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hα : 0 ≤ 1-1/N := by
    have hh : 1/N ≤ (1:ℝ) := (div_le_one hN0).mpr hN.le
    linarith
  have hβ : 0 ≤ 1/N := by positivity
  have hD := hθ.trans hθD
  unfold tau
  split_ifs with htzero htone
  · simp [distortionFloor, htzero]
  · exact (distortionFloor_le_time K N D t hD ht0).trans (by simp [htone])
  · calc
      distortionFloor K N D t = distortionFloor K N D t ^ (1/N+(1-1/N)) := by
        rw [show 1/N+(1-1/N) = (1:ℝ) by ring, ENNReal.rpow_one]
      _ = distortionFloor K N D t ^ (1/N) * distortionFloor K N D t ^ (1-1/N) :=
        ENNReal.rpow_add_of_nonneg _ _ hβ hα
      _ ≤ _ := mul_le_mul'
        (ENNReal.rpow_le_rpow (distortionFloor_le_time K N D t hD ht0) hβ)
        (ENNReal.rpow_le_rpow (distortionFloor_le_sigma K N D θ t hN hθ hθD ht0 ht1) hα)

end SinMulDivSinGe
section FullCD
open Set Filter MeasureTheory
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

 

theorem FullCD.ball_ratio_at_time
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (Metric.ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (p : X) (r R t : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (ht0 : 0 ≤ t) (htr : t*R < r) :
    distortionFloor K n (2*R) t ^ n * μ (Metric.ball p R) ≤ μ (Metric.ball p r) := by
  have hR : 0 < R := hr.trans_le hrR
  have ht1 : t < 1 := by nlinarith
  have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0:ℝ) < n := lt_trans zero_lt_one hn1
  let δ := (r-t*R)/(1+t)
  have hδ0 : 0 < δ := div_pos (sub_pos.mpr htr) (by linarith)
  have hδeq : δ*(1+t) = r-t*R := by dsimp [δ]; exact div_mul_cancel₀ _ (by linarith)
  have hδR : δ ≤ R := by nlinarith
  have hsmall0 : μ (Metric.ball p δ) ≠ 0 := (hpos p δ hδ0).ne'
  have hlarge0 : μ (Metric.ball p R) ≠ 0 := (hpos p R hR).ne'
  have hsmalltop : μ (Metric.ball p δ) ≠ ∞ := (hfin _ Metric.isBounded_ball).ne
  have hlargetop : μ (Metric.ball p R) ≠ ∞ := (hfin _ Metric.isBounded_ball).ne
  let T : Time := ⟨t, ht0, ht1.le⟩
  have hroot := hcd.support_volume_bound μ K n
    (Metric.ball p δ) (Metric.ball p R) (Metric.ball p r)
    Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet
    hsmall0 hsmalltop hlarge0 hlargetop
    (uniformOn_finiteSecondMoment μ _ Metric.isOpen_ball.measurableSet hsmall0 hsmalltop p δ
      (fun _ hx => le_of_lt hx))
    (uniformOn_finiteSecondMoment μ _ Metric.isOpen_ball.measurableSet hlarge0 hlargetop p R
      (fun _ hx => le_of_lt hx))
    n le_rfl hn1 T (distortionFloor K n (2*R) t)
    (by
      intro x hx y hy
      apply distortionFloor_le_tau K n (2*R) (dist x y) t hn1 dist_nonneg _ ht0 ht1.le
      have htri := dist_triangle x p y
      rw [dist_comm p y] at htri
      change dist x p < δ at hx
      change dist y p < R at hy
      linarith)
    (by
      intro γ hγ h₀ h₁
      have he : dist (γ T) (γ 0) = t*dist (γ 0) (γ 1) := by
        rw [hγ]
        change |t - 0| * dist (γ 0) (γ 1) = t * dist (γ 0) (γ 1)
        rw [sub_zero, abs_of_nonneg ht0]
      have htri := dist_triangle (γ T) (γ 0) p
      have hend := dist_triangle (γ 0) p (γ 1)
      rw [dist_comm p (γ 1)] at hend
      rw [he] at htri
      change dist (γ 0) p < δ at h₀
      change dist (γ 1) p < R at h₁
      change dist (γ T) p < r
      have hmul := mul_le_mul_of_nonneg_left hend ht0
      have hmul' := mul_le_mul_of_nonneg_left h₁.le ht0
      nlinarith)
  have hpow := ENNReal.rpow_le_rpow hroot hn0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hn0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, one_div_mul_cancel hn0.ne', ENNReal.rpow_one,
    ENNReal.rpow_one, ENNReal.rpow_natCast] at hpow
  exact hpow

 

theorem FullCD.ball_ratio
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (Metric.ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (p : X) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    distortionFloor K n (2*R) (r/R) ^ n * μ (Metric.ball p R) ≤ μ (Metric.ball p r) := by
  have hR : 0 < R := hr.trans_le hrR
  have ht : 0 < r/R := div_pos hr hR
  have hc : Continuous (fun t : ℝ => distortionFloor K n (2*R) t ^ n * μ (Metric.ball p R)) := by
    apply (ENNReal.continuous_mul_const (hfin _ Metric.isBounded_ball).ne).comp
    unfold distortionFloor
    simpa only [ENNReal.rpow_natCast, Function.comp_def, id_eq] using
      (ENNReal.continuous_rpow_const (y := (n:ℝ))).comp
        (ENNReal.continuous_ofReal.comp (continuous_id.div_const _))
  apply le_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto _ (𝓝[<] (r/R)) (𝓝 _))
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with t htr ht0
  exact hcd.ball_ratio_at_time μ K n hpos hfin hn p r R t hr hrR ht0.le
    ((lt_div_iff₀ hR).mp htr)

 theorem FullCD.flat_ball_ratio
    (μ : Measure X) [SigmaFinite μ] (n : ℕ) (hcd : FullCD μ 0 n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (Metric.ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (p : X) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ENNReal.ofReal (r/R)^n * μ (Metric.ball p R) ≤ μ (Metric.ball p r) := by
  simpa [distortionFloor] using hcd.ball_ratio μ 0 n hpos hfin hn p r R hr hrR

end FullCD
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

 

theorem FullCD.locDoubling (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ)
    (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) : IsUnifLocDoublingMeasure μ := by
  let C := ballGrowthConstant K n 1 ^ 2
  have hCt : C ≠ ∞ := ENNReal.pow_ne_top (ballGrowthConstant_ne_top K n 1)
  constructor
  refine ⟨C.toNNReal, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 4/9 by norm_num))] with r hr hrsmall
  change 0 < r at hr
  change r < 4/9 at hrsmall
  intro x
  rw [ENNReal.coe_toNNReal hCt]
  calc
    μ (closedBall x (2*r)) ≤ μ (ball x ((3/2:ℝ)^2*r)) := by
      apply measure_mono
      intro y hy
      change dist y x ≤ 2*r at hy
      exact lt_of_le_of_lt hy (by nlinarith)
    _ ≤ C * μ (ball x r) :=
      hcd.ball_growth_iterated μ K n hpos hfin hn x r 1 hr 2 (by nlinarith)
    _ ≤ C * μ (closedBall x r) := mul_le_mul' le_rfl (measure_mono ball_subset_closedBall)

 theorem NoncollapsedRCD.locDoubling (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) : IsUnifLocDoublingMeasure (hausdorff n X) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  exact hX.cd.locDoubling (hausdorff n X) K n hX.fullSupport hX.finiteOnBounded hn

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
 

theorem ediam_le_of_subset_closedBall {x : X} {r : ℝ} {s : Set X}
    (hs : s ⊆ closedBall x r) : ediam s ≤ ENNReal.ofReal (2*r) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro y hy z hz
  have hy' : dist y x ≤ r := hs hy
  have hz' : dist z x ≤ r := hs hz
  have ht := dist_triangle y x z
  rw [dist_comm x z] at ht
  linarith

 

theorem hausdorff_le_mul_measure_of_vitali [SecondCountableTopology X]
    (μ : Measure X) (v : VitaliFamily μ) (d : ℝ) (C : ℝ≥0∞)
    (s O : Set X) (habs : Measure.hausdorffMeasure d ≪ μ)
    (h : ∀ x ∈ s, ∀ ε : ℝ, 0 < ε → ∃ t : Set X,
      t ∈ v.setsAt x ∧ t ⊆ O ∧ t ⊆ closedBall x ε ∧
        ediam t ^ d ≤ C * μ t) :
    Measure.hausdorffMeasure d s ≤ C * μ O := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  let f : ℕ → X → Set (Set X) := fun n _ =>
    {t | t ⊆ O ∧ ediam t ≤ ENNReal.ofReal (a n) ∧ ediam t ^ d ≤ C * μ t}
  have hf (n : ℕ) : v.FineSubfamilyOn (f n) s := by
    intro x hx ε hε
    obtain ⟨t, htv, htO, htball, htcost⟩ := h x hx (min ε (a n/2)) (lt_min hε (half_pos (ha n)))
    refine ⟨t, ⟨htv, htO, ?_, htcost⟩, ?_⟩
    · exact (ediam_le_of_subset_closedBall htball).trans (ENNReal.ofReal_le_ofReal (by
        have := min_le_right ε (a n/2)
        linarith))
    · exact htball.trans (closedBall_subset_closedBall (min_le_left _ _))
  let A : ℕ → Set X := fun n => ⋃ p ∈ (hf n).index, (hf n).covering p
  have hnull (n : ℕ) : μ (s \ A n) = 0 := (hf n).measure_sdiff_biUnion
  let S := s \ ⋃ n, s \ A n
  have hHnull : Measure.hausdorffMeasure d (⋃ n, s \ A n) = 0 :=
    habs (measure_iUnion_null hnull)
  have hSeq : Measure.hausdorffMeasure d s = Measure.hausdorffMeasure d S :=
    (measure_sdiff_null hHnull).symm
  let ι : ℕ → Type _ := fun n => (hf n).index
  let (n : ℕ) : Countable (ι n) := (hf n).index_countable.to_subtype
  let t : ∀ n, ι n → Set X := fun n p => (hf n).covering p
  have hcover (n : ℕ) : S ⊆ ⋃ p, t n p := by
    intro x hx
    have hxA : x ∈ A n := by
      by_contra hn
      exact hx.2 (mem_iUnion.mpr ⟨n, hx.1, hn⟩)
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxA
    exact mem_iUnion.mpr ⟨⟨p,hp⟩, hxp⟩
  have hdiam (n : ℕ) (p : ι n) : ediam (t n p) ≤ ENNReal.ofReal (a n) :=
    ((hf n).covering_mem p.2).2.1
  have hsum (n : ℕ) : (∑' p : ι n, ediam (t n p)^d) ≤ C * μ O := by
    calc
      (∑' p : ι n, ediam (t n p)^d) ≤ ∑' p : ι n, C * μ (t n p) :=
        ENNReal.tsum_le_tsum fun p => ((hf n).covering_mem p.2).2.2
      _ = C * ∑' p : ι n, μ (t n p) := ENNReal.tsum_mul_left
      _ = C * μ (⋃ p : ι n, t n p) := by
        rw [measure_iUnion (hf n).covering_disjoint_subtype (fun p => (hf n).measurableSet_u p.2)]
      _ ≤ C * μ O := mul_le_mul' le_rfl (measure_mono (iUnion_subset fun p =>
        ((hf n).covering_mem p.2).1))
  have har : Tendsto (fun n => ENNReal.ofReal (a n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      (ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  rw [hSeq]
  exact (Measure.hausdorffMeasure_le_liminf_tsum d S (fun n => ENNReal.ofReal (a n)) har t
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)).trans
      (liminf_le_of_frequently_le (Eventually.of_forall hsum).frequently)

theorem volume_coefficient_le_of_ball_cost [SecondCountableTopology X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (n : ℕ) (c V D : ℝ≥0∞) (hc0 : c ≠ 0) (hV0 : V ≠ 0) (hVt : V ≠ ∞)
    (hμ : μ = c • Measure.hausdorffMeasure (n:ℝ))
    (O : Set X) (hO : IsOpen O) (hO0 : μ O ≠ 0) (hOt : μ O ≠ ∞)
    (hball : ∀ x ∈ O, ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      V * ENNReal.ofReal (2*r)^n ≤ D * μ (closedBall x r)) :
    V ≤ c*D := by
  have habs : Measure.hausdorffMeasure (n:ℝ) ≪ μ := by
    rw [hμ]
    exact Measure.absolutelyContinuous_smul hc0
  have hh : Measure.hausdorffMeasure (n:ℝ) O ≤ (D/V) * μ O := by
    apply hausdorff_le_mul_measure_of_vitali μ (IsUnifLocDoublingMeasure.vitaliFamily μ 1)
      (n:ℝ) (D/V) O O habs
    intro x hx ε hε
    obtain ⟨δ,hδ,hcost⟩ := hball x hx
    obtain ⟨η,hη,hsub⟩ := Metric.isOpen_iff.mp hO x hx
    let r := min ε (min δ (η/2))
    have hr : 0 < r := lt_min hε (lt_min hδ (half_pos hη))
    have hrδ : r ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
    have hrη : r < η := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
      (by linarith)
    refine ⟨closedBall x r, ?_, (closedBall_subset_ball hrη).trans hsub,
      closedBall_subset_closedBall (min_le_left _ _), ?_⟩
    · exact IsUnifLocDoublingMeasure.closedBall_mem_vitaliFamily_of_dist_le_mul μ
        (by simp only [dist_self, one_mul]; exact hr.le) hr
    · rw [ENNReal.rpow_natCast]
      have hpow := pow_le_pow_left' (ediam_le_of_subset_closedBall
        (subset_rfl : closedBall x r ⊆ closedBall x r)) n
      have hb := (mul_le_mul' (le_refl V) hpow).trans (hcost r hr hrδ)
      rw [show D/V * μ (closedBall x r) = (D*μ (closedBall x r))/V by
        simp only [div_eq_mul_inv]; ac_rfl]
      exact (ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVt)).mpr (by
        simpa only [mul_comm V] using hb)
  have hhV : V * Measure.hausdorffMeasure (n:ℝ) O ≤ D * μ O := by
    calc
      V * Measure.hausdorffMeasure (n:ℝ) O ≤ V * ((D/V) * μ O) := mul_le_mul' le_rfl hh
      _ = D * μ O := by rw [← mul_assoc, ENNReal.mul_div_cancel hV0 hVt]
  have hmass : μ O = c * Measure.hausdorffMeasure (n:ℝ) O := by
    rw [hμ, Measure.smul_apply, smul_eq_mul]
  apply (ENNReal.mul_le_mul_iff_left hO0 hOt).mp
  calc
    V*μ O = c*(V*Measure.hausdorffMeasure (n:ℝ) O) := by rw [hmass]; ac_rfl
    _ ≤ c*(D*μ O) := mul_le_mul' le_rfl hhV
    _ = (c*D)*μ O := (mul_assoc _ _ _).symm


end RegularPointCoordinates

end OAI
