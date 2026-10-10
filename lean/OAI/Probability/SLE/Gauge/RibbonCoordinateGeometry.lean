import OAI.Probability.SLE.Gauge.RibbonSurvival
import OAI.Probability.SLE.Geometry.PublishedPlanarDiskOpenness
import Mathlib.Analysis.Normed.Module.Connected

namespace OAI

/-! Coordinate balls in an embedded ribbon. These deterministic lemmas
turn the local lower Lipschitz bound into physical clearance, and identify
the future ribbon with part of the actual unbounded surviving component. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

/-- An open coordinate disk whose inverse has Lipschitz constant `K`
contains the physical disk of radius `r / K`. Compactness of the closed
coordinate disk prevents an interior physical point from escaping its image. -/
theorem ball_subset_image_ball
    (P : ℂ → ℂ) (x : ℂ) {r K : ℝ} (hr : 0 < r) (hK : 0 < K)
    (hP : ContinuousOn P (closedBall x r))
    (hopen : IsOpen (P '' ball x r))
    (hlower : ∀ y ∈ closedBall x r, dist y x ≤ K * dist (P y) (P x)) :
    ball (P x) (r / K) ⊆ P '' ball x r := by
  let A := P '' ball x r
  let Q := P '' closedBall x r
  have hQ : IsCompact Q := (isCompact_closedBall x r).image_of_continuousOn hP
  have hAQ : A ⊆ Q := image_mono ball_subset_closedBall
  have hsub : ball (P x) (r / K) ⊆ A ∪ Qᶜ := by
    intro z hz
    by_cases hzQ : z ∈ Q
    · left
      obtain ⟨y, hy, rfl⟩ := hzQ
      refine ⟨y, ?_, rfl⟩
      have hd := hlower y hy
      have hz' : dist (P y) (P x) < r / K := hz
      have hh := (lt_div_iff₀ hK).mp hz'
      exact lt_of_le_of_lt hd (by nlinarith [hh])
    · exact Or.inr hzQ
  apply IsPreconnected.subset_left_of_subset_union hopen hQ.isClosed.isOpen_compl
    (disjoint_compl_right.mono_left hAQ) hsub _ isPreconnected_ball
  exact ⟨P x, mem_ball_self (div_pos hr hK), mem_image_of_mem P (mem_ball_self hr)⟩

def closedRibbon : Set ℂ := {z | 0 ≤ z.re ∧ |z.im| ≤ 1}
def futureRibbon (k : ℝ) : Set ℂ := {z | k < z.re ∧ |z.im| < 1}

theorem futureRibbon_subset_closedRibbon {k : ℝ} (hk : 0 ≤ k) :
    futureRibbon k ⊆ closedRibbon := by
  intro z hz
  exact ⟨hk.trans hz.1.le, hz.2.le⟩

theorem futureRibbon_convex (k : ℝ) : Convex ℝ (futureRibbon k) := by
  have hre : Convex ℝ {z : ℂ | k < z.re} :=
    convex_halfSpace_gt Complex.reLm.isLinear k
  have him : Convex ℝ {z : ℂ | z.im ∈ Ioo (-1 : ℝ) 1} :=
    (convex_Ioo (-1 : ℝ) 1).is_linear_preimage Complex.imLm.isLinear
  simpa only [futureRibbon, abs_lt, mem_Ioo, ofPred_and] using hre.inter him

/-- Any unbounded connected free set belongs to the unbounded component
used in the actual Loewner surviving domain. -/
theorem free_preconnected_subset_surviving
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (S : Set ℂ)
    (hS : IsPreconnected S) (hfree : S ⊆ upperHalfPlane \ (γ '' Icc 0 T))
    (hunbounded : ¬ Bornology.IsBounded S) : S ⊆ survivingDomain γ T := by
  intro z hz
  refine ⟨hfree hz, ?_⟩
  intro hbounded
  exact hunbounded (hbounded.subset (hS.subset_connectedComponentIn hz hfree))

/-- Embedding excludes all nonlocal pieces of the stopped past from the
future ribbon. Escape to infinity places the whole future ribbon in the
surviving component, without assuming a filled-hull containment. -/
theorem futureRibbon_survives
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon)
    (hi : InjOn P closedRibbon) {k : ℝ} (hk : 0 ≤ k)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0)
    (hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k})
    (hunbounded : ¬ Bornology.IsBounded (P '' futureRibbon k)) :
    P '' futureRibbon k ⊆ survivingDomain γ T := by
  have hsub := futureRibbon_subset_closedRibbon hk
  apply free_preconnected_subset_surviving γ T _
    ((futureRibbon_convex k).isPreconnected.image P (hP.mono hsub)) _ hunbounded
  rintro z ⟨y, hy, rfl⟩
  refine ⟨hH y (hsub hy) (hk.trans_lt hy.1), ?_⟩
  intro hyPast
  obtain ⟨x, hx, he⟩ := hpast hyPast
  have hxy : x = y := hi hx.1 (hsub hy) he
  exact (not_le_of_gt hy.1) (hxy ▸ hx.2)

/-- A coordinate disk strictly ahead of the front and away from the two
ribbon edges gives a physical disk in the actual surviving domain. -/
theorem coordinate_ball_clearance
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon)
    (hi : InjOn P closedRibbon) {k : ℝ} (hk : 0 ≤ k)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0)
    (hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k})
    (hunbounded : ¬ Bornology.IsBounded (P '' futureRibbon k))
    (x : ℂ) {r K : ℝ} (hr : 0 < r) (hK : 0 < K)
    (hfront : k + r < x.re) (hedge : |x.im| + r < 1)
    (hopen : IsOpen (P '' ball x r))
    (hlower : ∀ y ∈ closedBall x r, dist y x ≤ K * dist (P y) (P x)) :
    ball (P x) (r / K) ⊆ survivingDomain γ T := by
  have hball : closedBall x r ⊆ futureRibbon k := by
    intro y hy
    have hd : ‖y - x‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hy
    have hre := (Complex.abs_re_le_norm (y - x)).trans hd
    have him := (Complex.abs_im_le_norm (y - x)).trans hd
    simp only [Complex.sub_re, Complex.sub_im] at hre him
    refine ⟨by linarith [(abs_le.mp hre).1], ?_⟩
    have htri : |y.im| ≤ |y.im - x.im| + |x.im| := by
      simpa only [sub_add_cancel] using abs_add_le (y.im - x.im) x.im
    linarith
  exact (ball_subset_image_ball P x hr hK
    (hP.mono (hball.trans (futureRibbon_subset_closedRibbon hk))) hopen hlower).trans
    ((image_mono (ball_subset_closedBall.trans hball)).trans
      (futureRibbon_survives P hP hi hk hH γ T hpast hunbounded))

/-- The paper's access guide, before applying the ribbon coordinate map. -/
def guideCoordinate (k x t : ℝ) : ℂ :=
  ((k + t : ℝ) : ℂ) + ((x * max (1 - 4 * t) 0 : ℝ) : ℂ) * Complex.I

@[simp] theorem guideCoordinate_re (k x t : ℝ) :
    (guideCoordinate k x t).re = k + t := by simp [guideCoordinate]

@[simp] theorem guideCoordinate_im (k x t : ℝ) :
    (guideCoordinate k x t).im = x * max (1 - 4 * t) 0 := by simp [guideCoordinate]

theorem guideCoordinate_continuous (k x : ℝ) : Continuous (guideCoordinate k x) := by
  unfold guideCoordinate
  fun_prop

theorem guideCoordinate_im_bound {k x t : ℝ} (ht : 0 ≤ t) :
    |(guideCoordinate k x t).im| ≤ |x| := by
  rw [guideCoordinate_im, abs_mul, abs_of_nonneg (le_max_right (1 - 4 * t) 0)]
  exact mul_le_of_le_one_right (abs_nonneg x) (max_le (by linarith) (by norm_num))

/-- The longitudinal coordinate gives the lower chord bound directly. -/
theorem guideCoordinate_lower_chord (k x u v : ℝ) :
    |u - v| ≤ dist (guideCoordinate k x u) (guideCoordinate k x v) := by
  have hh := Complex.abs_re_le_norm (guideCoordinate k x u - guideCoordinate k x v)
  simpa only [Complex.sub_re, guideCoordinate_re, add_sub_add_left_eq_sub,
    dist_eq_norm] using hh

theorem guideCoordinate_upper_chord (k x u v : ℝ) :
    dist (guideCoordinate k x u) (guideCoordinate k x v) ≤
      (1 + 4 * |x|) * |u - v| := by
  have hmax := abs_max_sub_max_le_abs (1 - 4 * u) (1 - 4 * v) 0
  have he : (1 - 4 * u) - (1 - 4 * v) = -4 * (u - v) := by ring
  rw [he, abs_mul] at hmax
  norm_num at hmax
  have him : |x * max (1 - 4 * u) 0 - x * max (1 - 4 * v) 0| ≤
      |x| * (4 * |u - v|) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hmax (abs_nonneg x)
  have hh := Complex.norm_le_abs_re_add_abs_im
    (guideCoordinate k x u - guideCoordinate k x v)
  simp only [Complex.sub_re, Complex.sub_im, guideCoordinate_re, guideCoordinate_im,
    add_sub_add_left_eq_sub] at hh
  rw [dist_eq_norm]
  nlinarith

def guideRadius (t : ℝ) : ℝ := min t 1 / 4

theorem guideRadius_pos {t : ℝ} (ht : 0 < t) : 0 < guideRadius t :=
  div_pos (lt_min ht zero_lt_one) (by norm_num)

/-- The guide is at most a quarter of the ribbon half-width from the
centerline; its coordinate disks have radius proportional to `min(t,1)`. -/
theorem guideCoordinate_disk_margins
    {k x t : ℝ} (hx : |x| ≤ 1 / 4) (ht : 0 < t) :
    k + guideRadius t < (guideCoordinate k x t).re ∧
      |(guideCoordinate k x t).im| + guideRadius t < 1 := by
  have hrt : guideRadius t ≤ t / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hr1 : guideRadius t ≤ 1 / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hi := (guideCoordinate_im_bound (k := k) (x := x) ht.le).trans hx
  rw [guideCoordinate_re]
  constructor <;> linarith

/-- Applying the coordinate disk lemma proves the paper's guide clearance
for every positive guide time, with the actual surviving domain. -/
theorem physical_guide_clearance
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon)
    (hi : InjOn P closedRibbon) {k x K : ℝ} (hk : 0 ≤ k)
    (hx : |x| ≤ 1 / 4) (hK : 0 < K)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0)
    (hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k})
    (hunbounded : ¬ Bornology.IsBounded (P '' futureRibbon k))
    (hopen : ∀ t ∈ Ioc (0 : ℝ) 2,
      IsOpen (P '' ball (guideCoordinate k x t) (guideRadius t)))
    (hlower : ∀ t ∈ Ioc (0 : ℝ) 2,
      ∀ y ∈ closedBall (guideCoordinate k x t) (guideRadius t),
        dist y (guideCoordinate k x t) ≤ K * dist (P y) (P (guideCoordinate k x t))) :
    ∀ t ∈ Ioc (0 : ℝ) 2,
      ball (P (guideCoordinate k x t)) (min t 1 / (4 * K)) ⊆ survivingDomain γ T := by
  intro t ht
  obtain ⟨hfront, hedge⟩ := guideCoordinate_disk_margins (k := k) hx ht.1
  have hh := coordinate_ball_clearance P hP hi hk hH γ T hpast hunbounded
    (guideCoordinate k x t) (guideRadius_pos ht.1) hK hfront hedge (hopen t ht) (hlower t ht)
  simpa only [guideRadius, div_div] using hh

/-- The fixed length-four patch appearing in the admissible ribbon class. -/
def guidePatch (k : ℝ) : Set ℂ := {z | k ≤ z.re ∧ z.re ≤ k + 3 ∧ |z.im| ≤ 1}

theorem guideCoordinate_disk_subset_patch
    {k x t : ℝ} (hx : |x| ≤ 1 / 4) (ht : t ∈ Ioc (0 : ℝ) 2) :
    closedBall (guideCoordinate k x t) (guideRadius t) ⊆ guidePatch k := by
  intro y hy
  have hd : ‖y - guideCoordinate k x t‖ ≤ guideRadius t := by
    simpa only [mem_closedBall, dist_eq_norm] using hy
  have hre := (Complex.abs_re_le_norm (y - guideCoordinate k x t)).trans hd
  have him := (Complex.abs_im_le_norm (y - guideCoordinate k x t)).trans hd
  simp only [Complex.sub_re, Complex.sub_im, guideCoordinate_re, guideCoordinate_im] at hre him
  obtain ⟨hfront, hedge⟩ := guideCoordinate_disk_margins (k := k) hx ht.1
  have hr1 : guideRadius t ≤ 1 / 4 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hi := (guideCoordinate_im_bound (k := k) (x := x) ht.1.le).trans hx
  have htri : |y.im| ≤ |y.im - (guideCoordinate k x t).im| +
      |(guideCoordinate k x t).im| := by
    simpa only [sub_add_cancel] using
      abs_add_le (y.im - (guideCoordinate k x t).im) (guideCoordinate k x t).im
  change k ≤ y.re ∧ y.re ≤ k + 3 ∧ |y.im| ≤ 1
  simp only [guideCoordinate_re] at hfront
  simp only [guideCoordinate_im] at htri hi
  exact ⟨by linarith [(abs_le.mp hre).1], by linarith [(abs_le.mp hre).2, ht.2],
    by linarith⟩

theorem guidePatch_subset_closedRibbon {k : ℝ} (hk : 0 ≤ k) :
    guidePatch k ⊆ closedRibbon := by
  intro z hz
  exact ⟨hk.trans hz.1, hz.2.2⟩

/-- The actual fixed patch inverse-Lipschitz bound suffices for all guide
disks. The only topological parameter is the cited planar disk theorem. -/
theorem physical_guide_clearance_of_patch
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon)
    (hi : InjOn P closedRibbon) {k x K : ℝ} (hk : 0 ≤ k)
    (hx : |x| ≤ 1 / 4) (hK : 0 < K)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0)
    (hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k})
    (hunbounded : ¬ Bornology.IsBounded (P '' futureRibbon k))
    (hlower : ∀ u ∈ guidePatch k, ∀ v ∈ guidePatch k,
      dist u v ≤ K * dist (P u) (P v)) :
    ∀ t ∈ Ioc (0 : ℝ) 2,
      ball (P (guideCoordinate k x t)) (min t 1 / (4 * K)) ⊆ survivingDomain γ T := by
  apply physical_guide_clearance P hP hi hk hx hK hH γ T hpast hunbounded
  · intro t ht
    have hsub := (ball_subset_closedBall.trans (guideCoordinate_disk_subset_patch hx ht)).trans
      (guidePatch_subset_closedRibbon hk)
    exact hpublished P _ _ (guideRadius_pos ht.1) (hP.mono hsub) (hi.mono hsub)
  · intro t ht y hy
    have hsub := guideCoordinate_disk_subset_patch (k := k) hx ht
    exact hlower y (hsub hy) _ (hsub (mem_closedBall_self (guideRadius_pos ht.1).le))

/-- Uniform clearance on every closed interval away from the tip is the
form used by joint physical/conformal guide compactness. -/
theorem physical_guide_clearance_away
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon)
    (hi : InjOn P closedRibbon) {k x K : ℝ} (hk : 0 ≤ k)
    (hx : |x| ≤ 1 / 4) (hK : 0 < K)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0)
    (hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k})
    (hunbounded : ¬ Bornology.IsBounded (P '' futureRibbon k))
    (hlower : ∀ u ∈ guidePatch k, ∀ v ∈ guidePatch k,
      dist u v ≤ K * dist (P u) (P v))
    {δ : ℝ} (hδ : 0 < δ) (_hδ2 : δ ≤ 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Icc δ 2,
      ball (P (guideCoordinate k x t)) r ⊆ survivingDomain γ T := by
  refine ⟨min δ 1 / (4 * K), div_pos (lt_min hδ zero_lt_one) (by positivity), ?_⟩
  intro t ht
  apply (ball_subset_ball ?_).trans (physical_guide_clearance_of_patch hpublished P hP hi
    hk hx hK hH γ T hpast hunbounded hlower t ⟨hδ.trans_le ht.1, ht.2⟩)
  exact div_le_div_of_nonneg_right (min_le_min_right 1 ht.1) (by positivity)

theorem guideCoordinate_mem_patch {k x t : ℝ}
    (hx : |x| ≤ 1 / 4) (ht : t ∈ Icc (0 : ℝ) 2) :
    guideCoordinate k x t ∈ guidePatch k := by
  change k ≤ (guideCoordinate k x t).re ∧
    (guideCoordinate k x t).re ≤ k + 3 ∧ |(guideCoordinate k x t).im| ≤ 1
  rw [guideCoordinate_re]
  exact ⟨by linarith [ht.1], by linarith [ht.2],
    (guideCoordinate_im_bound ht.1).trans (hx.trans (by norm_num))⟩

/-- The fixed coordinate patch speed bound gives the physical guide speed
bound required by the compactness and access-localization arguments. -/
theorem physical_guide_lipschitz
    (P : ℂ → ℂ) (C : ℝ≥0) {k x : ℝ} (hx : |x| ≤ 1 / 4)
    (hL : LipschitzOnWith C P (guidePatch k)) :
    LipschitzOnWith (2 * C) (fun t => P (guideCoordinate k x t)) (Icc (0 : ℝ) 2) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro u hu v hv
  have hp := hL.dist_le_mul _ (guideCoordinate_mem_patch hx hu) _
    (guideCoordinate_mem_patch hx hv)
  have hq := guideCoordinate_upper_chord k x u v
  have hcq : dist (guideCoordinate k x u) (guideCoordinate k x v) ≤ 2 * |u - v| := by
    exact hq.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hcq C.coe_nonneg
  simp only [NNReal.coe_mul, NNReal.coe_ofNat, Real.dist_eq]
  nlinarith

/-- The lower patch Lipschitz bound makes the physical guide uniformly
simple, including its initial boundary point. -/
theorem physical_guide_lower_chord
    (P : ℂ → ℂ) {k x K : ℝ} (hx : |x| ≤ 1 / 4) (hK : 0 < K)
    (hlower : ∀ u ∈ guidePatch k, ∀ v ∈ guidePatch k,
      dist u v ≤ K * dist (P u) (P v)) :
    ∀ u ∈ Icc (0 : ℝ) 2, ∀ v ∈ Icc (0 : ℝ) 2,
      (1 / K) * |u - v| ≤ dist (P (guideCoordinate k x u)) (P (guideCoordinate k x v)) := by
  intro u hu v hv
  have hh := (guideCoordinate_lower_chord k x u v).trans
    (hlower _ (guideCoordinate_mem_patch hx hu) _ (guideCoordinate_mem_patch hx hv))
  rw [one_div_mul_eq_div, div_le_iff₀ hK]
  simpa only [mul_comm] using hh

@[simp] theorem guideCoordinate_zero (k x : ℝ) :
    guideCoordinate k x 0 = (k : ℂ) + (x : ℂ) * Complex.I := by simp [guideCoordinate]

@[simp] theorem guideCoordinate_waypoint (k x : ℝ) :
    guideCoordinate k x (1 / 2) = ((k + 1 / 2 : ℝ) : ℂ) := by
  norm_num [guideCoordinate]

/-- The paper's escape condition on the centerline supplies the
unboundedness used to select the actual surviving component. -/
theorem futureRibbon_unbounded_of_centerline_escape
    (P : ℂ → ℂ) (k : ℝ)
    (hescape : Tendsto (fun s : ℝ => ‖P (s : ℂ)‖) atTop atTop) :
    ¬ Bornology.IsBounded (P '' futureRibbon k) := by
  intro hb
  obtain ⟨R, _, hR⟩ := hb.exists_pos_norm_lt
  obtain ⟨s, hs, hsR⟩ := ((eventually_gt_atTop k).and
    (hescape.eventually (eventually_gt_atTop R))).exists
  have hz : (s : ℂ) ∈ futureRibbon k := by
    change k < (s : ℂ).re ∧ |(s : ℂ).im| < 1
    simpa using And.intro hs (by norm_num : |(0 : ℝ)| < 1)
  exact (not_lt_of_ge hsR.le) (hR _ (mem_image_of_mem P hz))

end SLEExactGauge.RibbonCoordinates

end

end OAI
