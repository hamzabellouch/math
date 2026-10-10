import OAI.Probability.SLE.Gauge.RibbonPassageNeighborhood

namespace OAI

/-! Deterministic ribbon regions used by the limiting splice. The envelope
extends beyond the attained front, while its front slice is narrowed to
supply the prescribed physical terminal tolerance. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

def passageCoordinateRegion (C : ℝ≥0) (ε η : ℝ) : Set ℂ :=
  {w | -(1 / 4 : ℝ) < w.re ∧ w.re < 2 ∧ |w.im| < ε ∧
    (w.re < 1 / 2 ∨ |w.im| < η / (4 * (C : ℝ)))}

def physicalPassageRegion (P : ℂ → ℂ) (K : Set ℂ) (C : ℝ≥0) (ε η : ℝ) : Set ℂ :=
  P '' (K ∩ passageCoordinateRegion C ε η)

theorem passageCoordinateRegion_isOpen (C : ℝ≥0) (ε η : ℝ) :
    IsOpen (passageCoordinateRegion C ε η) := by
  apply IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
  apply IsOpen.inter (isOpen_lt Complex.continuous_re continuous_const)
  apply IsOpen.inter (isOpen_lt Complex.continuous_im.abs continuous_const)
  exact (isOpen_lt Complex.continuous_re continuous_const).union
    (isOpen_lt Complex.continuous_im.abs continuous_const)

/-- The prescribed access guide stays in the envelope, with its entire
late part on the centerline, independently of the terminal tolerance. -/
theorem guideCoordinate_mem_passageRegion
    (C : ℝ≥0) (hC : 0 < C) {ε η x t : ℝ}
    (hx : |x| < ε) (hη : 0 < η) (ht : t ∈ Icc (0 : ℝ) (3 / 2)) :
    guideCoordinate 0 x t ∈ passageCoordinateRegion C ε η := by
  have him := (guideCoordinate_im_bound (k := 0) (x := x) ht.1).trans_lt hx
  refine ⟨by rw [guideCoordinate_re]; linarith [ht.1],
    by rw [guideCoordinate_re]; linarith [ht.2], him, ?_⟩
  by_cases hsmall : t < 1 / 2
  · left
    simpa only [guideCoordinate_re, zero_add] using hsmall
  · right
    have htlarge : 1 / 2 ≤ t := le_of_not_gt hsmall
    have him0 : (guideCoordinate 0 x t).im = 0 := by
      rw [guideCoordinate_im, max_eq_right (by linarith), mul_zero]
    rw [him0, abs_zero]
    exact div_pos hη (mul_pos (by norm_num) hC)

/-- The thin front slice gives the terminal physical tolerance required by
`FrontSuccess`, using the actual upper patch Lipschitz constant. -/
theorem physicalPassageRegion_terminal
    (P : ℂ → ℂ) (K : Set ℂ) (C L : ℝ≥0) (ε η : ℝ)
    (hC : 0 < C) (hupper : LipschitzOnWith C P K)
    (hlower : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ L * dist (P x) (P y))
    (hbase : (1 : ℂ) ∈ K) {z : ℂ}
    (hz : z ∈ physicalPassageRegion P K C ε η)
    (hp : longitudinalCoordinate P K 0 z = 1) :
    ‖z - P 1‖ < η / 4 := by
  obtain ⟨w, ⟨hwK, hwV⟩, rfl⟩ := hz
  have hi := lower_lipschitz_injOn P K L hlower
  have hwre : w.re = 1 := by
    simpa only [longitudinalCoordinate, coordinateInverse_left hi hwK, sub_zero] using hp
  have him : |w.im| < η / (4 * (C : ℝ)) := by
    rcases hwV.2.2.2 with hsmall | hthin
    · rw [hwre] at hsmall
      norm_num at hsmall
    · exact hthin
  have hd : dist w (1 : ℂ) = |w.im| := by
    have he : w - 1 = (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hwre]
    rw [dist_eq_norm, he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hbound := hupper.dist_le_mul w hwK 1 hbase
  rw [hd] at hbound
  have hCpos : 0 < (C : ℝ) := hC
  have hthin : (C : ℝ) * |w.im| < η / 4 := by
    have hh := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hCpos)).mp him
    linarith
  simpa only [dist_eq_norm] using hbound.trans_lt hthin

/-- The actual limiting guide supplies a common physical neighborhood and
all varying-region conditions used by the retained-mass passage theorem. -/
theorem limiting_guide_passage_neighborhood
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K : Set ℂ) (C L : ℝ≥0)
    (hC : 0 < C) (hL : 0 < L)
    (hupper : ∀ n, LipschitzOnWith C (Pₙ n) K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hP : ContinuousOn P K) (hPH : MapsTo P (interior K) upperHalfPlane)
    (α : ℝ → ℂ) (hα : ContinuousOn α (Icc 0 2)) (x ε η : ℝ)
    (hx : |x| < ε) (hη : 0 < η)
    (hshape : EqOn α (fun t => P (guideCoordinate 0 x t)) (Icc 0 2))
    (hmem : ∀ t ∈ Icc (0 : ℝ) (3 / 2), guideCoordinate 0 x t ∈ interior K)
    (hbase : (1 : ℂ) ∈ K) :
    ∃ U : Set ℂ, IsOpen U ∧ α '' Icc (0 : ℝ) (3 / 2) ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ P '' interior K ∧
      U ⊆ upperHalfPlane ∧
      ContinuousOn (longitudinalCoordinate P K 0) U ∧
      (∀ᶠ n in atTop, ContinuousOn (longitudinalCoordinate (Pₙ n) K 0) U) ∧
      TendstoLocallyUniformlyOn (fun n => longitudinalCoordinate (Pₙ n) K 0)
        (longitudinalCoordinate P K 0) atTop U ∧
      (∀ᶠ n in atTop, U ⊆ physicalPassageRegion (Pₙ n) K C ε η) ∧
      (∀ n z, z ∈ physicalPassageRegion (Pₙ n) K C ε η →
        longitudinalCoordinate (Pₙ n) K 0 z = 1 → ‖z - Pₙ n 1‖ < η / 4) ∧
      (∀ᶠ n in atTop,
        U ∩ {z | (1 / 3 : ℝ) < longitudinalCoordinate (Pₙ n) K 0 z ∧
          longitudinalCoordinate (Pₙ n) K 0 z < 2 / 3} ⊆ physicalMiddleRegion (Pₙ n) K 0 ε) := by
  let V := passageCoordinateRegion C ε η
  let A := α '' Icc (0 : ℝ) (3 / 2)
  have hA : IsCompact A := isCompact_Icc.image_of_continuousOn
    (hα.mono (Icc_subset_Icc_right (by norm_num)))
  have hAV : A ⊆ P '' (interior K ∩ V) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨guideCoordinate 0 x t, ⟨hmem t ht,
      guideCoordinate_mem_passageRegion C hC hx hη ht⟩,
      (hshape ⟨ht.1, ht.2.trans (by norm_num)⟩).symm⟩
  obtain ⟨U, hU, hAU, hUc, hUPV, hVlate, hKlate, _⟩ :=
    common_coordinate_region_neighborhood hpublished Pₙ P K A V L hL hP
      (fun n => (hupper n).continuousOn) hconv hlower hA
      (passageCoordinateRegion_isOpen C ε η) hAV
  have hUP : closure U ⊆ P '' interior K := hUPV.trans (image_mono inter_subset_left)
  have hlim := lower_lipschitz_uniform_limit Pₙ P K L hconv hlower
  have hi := lower_lipschitz_injOn P K L hlim
  have hwidth : ∀ z ∈ closure U, |(coordinateInverse P K z).im| < ε := by
    intro z hz
    obtain ⟨w, hw, he⟩ := hUPV hz
    rw [← he, coordinateInverse_left hi (interior_subset hw.1)]
    exact hw.2.2.2.1
  refine ⟨U, hU, hAU, hUc, hUP, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (subset_closure.trans hUP).trans (image_subset_iff.mpr hPH)
  · exact (longitudinalCoordinate_continuousOn P K L 0 hlim).mono
      (subset_closure.trans (hUP.trans (image_mono interior_subset)))
  · filter_upwards [hKlate] with n hn
    exact (longitudinalCoordinate_continuousOn (Pₙ n) K L 0 (hlower n)).mono
      (subset_closure.trans (hn.trans (image_mono interior_subset)))
  · exact (longitudinalCoordinate_locally_uniform hpublished Pₙ P K L 0 hL hP
      (fun n => (hupper n).continuousOn) hconv hlower).mono (subset_closure.trans hUP)
  · exact hVlate.mono (fun _ hn => subset_closure.trans hn)
  · exact fun n z hz hp => physicalPassageRegion_terminal (Pₙ n) K C L ε η hC
      (hupper n) (hlower n) hbase hz hp
  · exact eventual_middle_region_inclusion Pₙ P K U L 0 ε hconv hlower hUc
      (hUP.trans (image_mono interior_subset))
      (hKlate.mono (fun _ hn => hn.trans (image_mono interior_subset))) hwidth

/-- Local coordinate convergence and convergence of the starting tips
supply the fixed early ball used by localization. -/
theorem eventual_early_coordinate_ball
    (pₙ : ℕ → ℂ → ℝ) (p : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hp : ContinuousOn p U) (hconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (aₙ : ℕ → ℂ) (a : ℂ) (ha : a ∈ U) (hpa : p a = 0)
    (halim : Tendsto aₙ atTop (𝓝 a)) :
    ∃ r : ℝ, 0 < r ∧ ball a (r / 2) ⊆ U ∧
      (∀ z ∈ ball a (r / 4), p z < 1 / 3) ∧
      ∀ᶠ n in atTop, ball (aₙ n) r ⊆ U ∩ {z | pₙ n z < 1} := by
  let W := U ∩ p ⁻¹' Iio (1 / 6 : ℝ)
  have hW : IsOpen W := hp.isOpen_inter_preimage hU isOpen_Iio
  have haW : a ∈ W := ⟨ha, by simp only [mem_preimage, mem_Iio, hpa]; norm_num⟩
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hW a haW
  let r := d / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let C := closedBall a (d / 2)
  have hCW : C ⊆ W := by
    intro z hz
    have hz' : dist z a ≤ d / 2 := hz
    exact hball (hz'.trans_lt (by linarith))
  have hCU : C ⊆ U := hCW.trans inter_subset_left
  have hu : TendstoUniformlyOn pₙ p atTop C :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall a (d / 2))).mp (hconv.mono hCU)
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · intro z hz
    have hrd : r / 2 < d := by dsimp only [r]; linarith
    exact (hball (lt_trans hz hrd)).1
  · intro z hz
    have hrd : r / 4 < d := by dsimp only [r]; linarith
    have hh := (hball (lt_trans hz hrd)).2
    exact hh.trans (by norm_num)
  · filter_upwards [halim.eventually (Metric.ball_mem_nhds a hr),
      Metric.tendstoUniformlyOn_iff.mp hu (1 / 6) (by norm_num)] with n hn hclose
    intro z hz
    have hza : dist z a < d / 2 := by
      have hh := (dist_triangle z (aₙ n) a).trans_lt (add_lt_add hz hn)
      dsimp [r] at hh
      linarith
    have hzC : z ∈ C := hza.le
    have hc := hclose z hzC
    rw [Real.dist_eq] at hc
    have hpz := (hCW hzC).2
    refine ⟨hCU hzC, ?_⟩
    have habs := (abs_lt.mp hc).1
    change p z < 1 / 6 at hpz
    change pₙ n z < 1
    linarith

end SLEExactGauge.RibbonCoordinates

end

end OAI
