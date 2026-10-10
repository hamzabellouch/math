import OAI.Probability.SLE.Geometry.CompleteAccessGuide
import OAI.Probability.SLE.Geometry.WaypointCrosscutSides

namespace OAI

/-! The local straightening hypotheses at the actual ribbon waypoint.
The complete access guide and the inverse identities exclude nonlocal
pieces of the guide from the waypoint disk. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

theorem waypoint_ball_coordinates {k : ℝ} {z : ℂ}
    (hz : z ∈ ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)) :
    k + 1 / 4 < z.re ∧ z.re < k + 3 / 4 ∧ |z.im| < 1 / 4 := by
  have hd : ‖z - ((k + 1 / 2 : ℝ) : ℂ)‖ < 1 / 4 := by
    simpa only [mem_ball, dist_eq_norm] using hz
  have hr := (Complex.abs_re_le_norm (z - ((k + 1 / 2 : ℝ) : ℂ))).trans_lt hd
  have hi := (Complex.abs_im_le_norm (z - ((k + 1 / 2 : ℝ) : ℂ))).trans_lt hd
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
  exact ⟨by linarith [(abs_lt.mp hr).1], by linarith [(abs_lt.mp hr).2], hi⟩

theorem guideCoordinate_mem_future {k x : ℝ} (hx : |x| ≤ 1 / 4)
    {t : ℝ} (ht : 0 < t) : guideCoordinate k x t ∈ futureRibbon k := by
  exact ⟨by simp only [guideCoordinate_re]; linarith,
    (guideCoordinate_im_bound ht.le).trans_lt (hx.trans_lt (by norm_num))⟩

/-- The complete straightening detects the whole physical access guide,
including points far outside the local coordinate disk. -/
theorem actual_straightened_zero_lies_on_guide
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (P : ℂ → ℂ) {k x : ℝ} (hx : |x| ≤ 1 / 4)
    (hfuture : P '' futureRibbon k ⊆ survivingDomain γ T)
    (β : ℝ≥0 → ℂ)
    (hβ : ∀ t : ℝ≥0, 0 < t →
      β t = G T (P (guideCoordinate k x t)) - (U T : ℂ))
    (h : ℂ ≃ₜ ℂ) (hH : MapsTo h upperHalfPlane upperHalfPlane)
    (hstraight : ∀ t : ℝ≥0, h (β t) = (t : ℂ) * Complex.I)
    {z : ℂ} (hz : z ∈ survivingDomain γ T)
    (hzero : (h (G T z - (U T : ℂ))).re = 0) :
    ∃ t : ℝ, 0 < t ∧ P (guideCoordinate k x t) = z := by
  have hzH : G T z - (U T : ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im,
      sub_zero] using hw.imag_positive T z hz
  obtain ⟨t, ht, he⟩ :=
    (CrosscutSides.straightened_real_zero_iff β h hH hstraight hzH).mp hzero
  have hD := hfuture (mem_image_of_mem P (guideCoordinate_mem_future hx (by exact_mod_cast ht)))
  have hg : G T (P (guideCoordinate k x t)) = G T z := by
    rw [hβ t ht] at he
    exact sub_left_inj.mp he
  refine ⟨t, by exact_mod_cast ht, ?_⟩
  calc
    P (guideCoordinate k x t) = F T (G T (P (guideCoordinate k x t))) :=
      (hw.2.2.2.2.2.2.2.1 T _ hD).symm
    _ = F T (G T z) := congrArg (F T) hg
    _ = z := hw.2.2.2.2.2.2.2.1 T z hz

theorem actual_waypoint_chart
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hiP : InjOn P closedRibbon)
    {k x : ℝ} (hk : 0 ≤ k) (hx : |x| ≤ 1 / 4)
    (hfuture : P '' futureRibbon k ⊆ survivingDomain γ T)
    (β : ℝ≥0 → ℂ)
    (hβ : ∀ t : ℝ≥0, 0 < t →
      β t = G T (P (guideCoordinate k x t)) - (U T : ℂ))
    (h : ℂ ≃ₜ ℂ) (hH : MapsTo h upperHalfPlane upperHalfPlane)
    (hstraight : ∀ t : ℝ≥0, h (β t) = (t : ℂ) * Complex.I) :
    let f := fun z => h (G T (P z) - (U T : ℂ))
    ContinuousOn f (ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)) ∧
      InjOn f (ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)) ∧
      ∀ z ∈ ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4), (f z).re = 0 ↔ z.im = 0 := by
  dsimp only
  let B := ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)
  have hBF : B ⊆ futureRibbon k := by
    intro z hz
    obtain ⟨hr, _, him⟩ := waypoint_ball_coordinates hz
    exact ⟨by linarith, him.trans (by norm_num)⟩
  have hBC := hBF.trans (futureRibbon_subset_closedRibbon hk)
  have hBD : MapsTo P B (survivingDomain γ T) := by
    intro z hz
    exact hfuture (mem_image_of_mem P (hBF hz))
  have hclosed (t : ℝ≥0) (ht : 0 < t) :
      guideCoordinate k x t ∈ closedRibbon :=
    futureRibbon_subset_closedRibbon hk (guideCoordinate_mem_future hx (by exact_mod_cast ht))
  have hD (t : ℝ≥0) (ht : 0 < t) :
      P (guideCoordinate k x t) ∈ survivingDomain γ T :=
    hfuture (mem_image_of_mem P (guideCoordinate_mem_future hx (by exact_mod_cast ht)))
  have hgInj : InjOn (G T) (survivingDomain γ T) := by
    intro z hz w hw' he
    calc
      z = F T (G T z) := (hw.2.2.2.2.2.2.2.1 T z hz).symm
      _ = F T (G T w) := congrArg (F T) he
      _ = w := hw.2.2.2.2.2.2.2.1 T w hw'
  refine ⟨h.continuous.continuousOn.comp
    (((hw.2.2.2.1 T).continuousOn.comp (hP.mono hBC) hBD).sub continuousOn_const)
    (fun _ _ => mem_univ _), ?_, ?_⟩
  · intro z hz w hw' he
    exact hiP (hBC hz) (hBC hw')
      (hgInj (hBD hz) (hBD hw') (sub_left_inj.mp (h.injective he)))
  · intro z hz
    have hzH : G T (P z) - (U T : ℂ) ∈ upperHalfPlane := by
      simpa only [upperHalfPlane, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im,
        sub_zero] using hw.imag_positive T (P z) (hBD hz)
    rw [CrosscutSides.straightened_real_zero_iff β h hH hstraight hzH]
    constructor
    · rintro ⟨t, ht, he⟩
      rw [hβ t ht] at he
      have hcoord : guideCoordinate k x t = z :=
        hiP (hclosed t ht) (hBC hz) (hgInj (hD t ht) (hBD hz) (sub_left_inj.mp he))
      have hre := congrArg Complex.re hcoord
      simp only [guideCoordinate_re] at hre
      have htquarter : 1 / 4 < (t : ℝ) := by
        linarith [(waypoint_ball_coordinates hz).1]
      rw [← hcoord, guideCoordinate_im, max_eq_right (by linarith), mul_zero]
    · intro him
      let t : ℝ≥0 := ⟨z.re - k, by linarith [(waypoint_ball_coordinates hz).1]⟩
      have ht : 0 < t := by
        change 0 < z.re - k
        linarith [(waypoint_ball_coordinates hz).1]
      have he : guideCoordinate k x t = z := by
        apply Complex.ext
        · rw [guideCoordinate_re]
          change k + (z.re - k) = z.re
          ring
        · rw [guideCoordinate_im, max_eq_right, mul_zero, him]
          change 1 - 4 * (z.re - k) ≤ 0
          linarith [(waypoint_ball_coordinates hz).1]
      exact ⟨t, ht, by rw [hβ t ht, he]⟩

/-- The actual complete physical guide is proper because its tail is the
centerline; no compactness or properness of a parameter guide is assumed. -/
theorem actual_ribbon_complete_guide
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (hT : 0 < T)
    (hfresh : ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hiP : InjOn P closedRibbon)
    {k x : ℝ} (hk : 0 ≤ k) (hx : |x| ≤ 1 / 4)
    (htip : P ((k : ℂ) + (x : ℂ) * Complex.I) = γ T)
    (hfuture : P '' futureRibbon k ⊆ survivingDomain γ T)
    (hescape : Tendsto (fun s : ℝ => ‖P (s : ℂ)‖) atTop atTop) :
    ∃ β : ℝ≥0 → ℂ, Continuous β ∧ Function.Injective β ∧ β 0 = 0 ∧
      (∀ t : ℝ≥0, 0 < t → β t ∈ upperHalfPlane) ∧
      Tendsto β atTop (cocompact ℂ) ∧
      ∀ t : ℝ≥0, 0 < t → β t = G T (P (guideCoordinate k x t)) - (U T : ℂ) := by
  let α : ℝ≥0 → ℂ := fun t => P (guideCoordinate k x t)
  have hgc (t : ℝ≥0) : guideCoordinate k x t ∈ closedRibbon := by
    exact ⟨by simp only [guideCoordinate_re]; positivity,
      (guideCoordinate_im_bound t.coe_nonneg).trans (hx.trans (by norm_num))⟩
  have hα : Continuous α :=
    hP.comp_continuous ((guideCoordinate_continuous k x).comp NNReal.continuous_coe)
      hgc
  have hiα : Function.Injective α := by
    intro s t he
    have hh := congrArg Complex.re (hiP (hgc s) (hgc t) he)
    simp only [guideCoordinate_re] at hh
    apply NNReal.eq
    linarith
  have hα0 : α 0 = γ T := by simpa only [α, NNReal.coe_zero, guideCoordinate_zero] using htip
  have hαD (t : ℝ≥0) (ht : 0 < t) : α t ∈ survivingDomain γ T :=
    hfuture (mem_image_of_mem P (guideCoordinate_mem_future hx (by exact_mod_cast ht)))
  have htend : Tendsto (fun t : ℝ≥0 => k + (t : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ k (NNReal.tendsto_coe_atTop.mpr tendsto_id)
  have hnorm : Tendsto (fun t => ‖α t‖) atTop atTop := by
    apply (hescape.comp htend).congr'
    filter_upwards [(NNReal.tendsto_coe_atTop.mpr tendsto_id).eventually_ge_atTop
      (1 / 4 : ℝ)] with t ht
    simp only [id_eq] at ht
    change ‖P ((k + (t : ℝ) : ℝ) : ℂ)‖ = ‖P (guideCoordinate k x t)‖
    apply congrArg (fun z : ℂ => ‖P z‖)
    apply Complex.ext
    · simp [guideCoordinate]
    · simp only [guideCoordinate_im, Complex.ofReal_im]
      rw [max_eq_right (by linarith), mul_zero]
  have hproper : Tendsto α atTop (cocompact ℂ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop 0
    simpa only [dist_zero_right] using hnorm
  exact actual_complete_access_guide hw hU T hT hfresh α hα hiα hα0 hαD hproper

theorem actual_ribbon_waypoint_straightening
    (hpublished : PublishedHalfPlaneCrosscutStraightening)
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (hT : 0 < T)
    (hfresh : ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hiP : InjOn P closedRibbon)
    {k x : ℝ} (hk : 0 ≤ k) (hx : |x| ≤ 1 / 4)
    (htip : P ((k : ℂ) + (x : ℂ) * Complex.I) = γ T)
    (hfuture : P '' futureRibbon k ⊆ survivingDomain γ T)
    (hescape : Tendsto (fun s : ℝ => ‖P (s : ℂ)‖) atTop atTop) :
    ∃ h : ℂ ≃ₜ ℂ, (∀ y : ℝ, h (y : ℂ) = (y : ℂ)) ∧
      MapsTo h upperHalfPlane upperHalfPlane ∧
      (∀ z ∈ survivingDomain γ T, (h (G T z - (U T : ℂ))).re = 0 →
        ∃ u : ℝ, 0 ≤ u ∧ P (guideCoordinate k x u) = z) ∧
      let f := fun z => h (G T (P z) - (U T : ℂ))
      ContinuousOn f (ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)) ∧
        InjOn f (ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)) ∧
        ∀ z ∈ ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4), (f z).re = 0 ↔ z.im = 0 := by
  obtain ⟨β, hc, hi, hz, hH, hproper, heq⟩ :=
    actual_ribbon_complete_guide hw hU T hT hfresh P hP hiP hk hx htip hfuture hescape
  obtain ⟨h, hreal, hhalf, hstraight⟩ := hpublished β hc hi hz hH hproper
  refine ⟨h, hreal, hhalf, ?_, actual_waypoint_chart hw T P hP hiP hk hx hfuture β
    heq h hhalf hstraight⟩
  intro z hz hzero
  obtain ⟨u, hu, he⟩ := actual_straightened_zero_lies_on_guide hw T P hx hfuture
    β heq h hhalf hstraight hz hzero
  exact ⟨u, hu.le, he⟩

/-- Actual physical waypoint neighborhoods lie on opposite sides of the
complete stopped access guide. The orientation is selected by the local
chart and is shared by the whole pair of neighborhoods. -/
theorem actual_physical_waypoint_tubes_opposite_sides
    (hpublished : PublishedHalfPlaneCrosscutStraightening)
    (hopen : PublishedPlanarDiskOpenness)
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (hT : 0 < T)
    (hfresh : ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hiP : InjOn P closedRibbon)
    {k x : ℝ} (hk : 1 ≤ k) (hx : |x| ≤ 1 / 4)
    (htip : P ((k : ℂ) + (x : ℂ) * Complex.I) = γ T)
    (hfuture : P '' futureRibbon k ⊆ survivingDomain γ T)
    (hescape : Tendsto (fun s : ℝ => ‖P (s : ℂ)‖) atTop atTop)
    (K : ℝ≥0) (hK : 0 < (K : ℝ))
    (hlower : ∀ v ∈ crossingPatch k, ∀ w ∈ crossingPatch k,
      dist v w ≤ K * dist (P v) (P w)) :
    ∃ (h : ℂ ≃ₜ ℂ) (side : ℝ),
      (∀ y : ℝ, h (y : ℂ) = (y : ℂ)) ∧
      MapsTo h upperHalfPlane upperHalfPlane ∧
      (side = -1 ∨ side = 1) ∧
      (∀ y : ℂ, dist y (P (waypointRoute k side (1 / 4))) < (1 / 32 : ℝ) / K →
        0 < (h (G T y - (U T : ℂ))).re) ∧
      (∀ y : ℂ, dist y (P (waypointRoute k (-side) (1 / 4))) < (1 / 32 : ℝ) / K →
        (h (G T y - (U T : ℂ))).re < 0) := by
  obtain ⟨h, hreal, hH, _, hc, hi, hzero⟩ := actual_ribbon_waypoint_straightening
    hpublished hw hU T hT hfresh P hP hiP (by linarith) hx htip hfuture hescape
  obtain ⟨side, hs, hp, hn⟩ := physical_waypoint_tubes_opposite_sides
    hopen P hP hiP K hK hk hlower
    (fun z => h (G T (P z) - (U T : ℂ)))
    (fun y => (h (G T y - (U T : ℂ))).re) hc hi hzero (fun _ _ => rfl)
  exact ⟨h, side, hreal, hH, hs, hp, hn⟩

end SLEExactGauge.RibbonCoordinates

end

end OAI
