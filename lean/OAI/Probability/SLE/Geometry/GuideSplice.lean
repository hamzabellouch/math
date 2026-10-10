import OAI.Probability.SLE.Geometry.SmallImageSector

namespace OAI

/-!
The deterministic last-crossing and connector geometry following
`es:good-semicircle`. All sets below are actual subsets of the complex plane.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
open scoped unitInterval

namespace SLEExactGauge.GuideSplice

/-- The final crossing of a small circle occurs before the specified positive
time; the remainder of the guide lies strictly outside that circle. -/
theorem exists_last_circle_crossing
    {β : ℝ → ℂ} {B δ T : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδT : δ ≤ T)
    (hβ : ContinuousOn β (Icc 0 T)) (hβ₀ : β 0 = 0)
    (hlate : ∀ t ∈ Icc δ T, B < ‖β t‖) :
    ∃ tB ∈ Ioo 0 δ, ‖β tB‖ = B ∧
      ∀ t ∈ Ioc tB T, B < ‖β t‖ := by
  have hT : 0 < T := hδ.trans_le hδT
  have hBT := hlate T ⟨hδT, le_rfl⟩
  let K := Icc 0 T ∩ (fun t => ‖β t‖) ⁻¹' {B}
  have hKclosed : IsClosed K :=
    hβ.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hKcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed inter_subset_left
  have hKnonempty : K.Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hT.le hβ.norm
      (show B ∈ Icc ‖β 0‖ ‖β T‖ by simpa [hβ₀] using And.intro hB.le hBT.le)
    exact ⟨t, ht, he⟩
  obtain ⟨tB, htB, hmax⟩ := hKcompact.exists_isGreatest hKnonempty
  have heB : ‖β tB‖ = B := htB.2
  have htBpos : 0 < tB := by
    by_contra hn
    have he : tB = 0 := le_antisymm (le_of_not_gt hn) htB.1.1
    rw [he, hβ₀, norm_zero] at heB
    exact hB.ne' heB.symm
  have htBδ : tB < δ := by
    by_contra hn
    have hh := hlate tB ⟨le_of_not_gt hn, htB.1.2⟩
    exact (ne_of_gt hh) heB
  refine ⟨tB, ⟨htBpos, htBδ⟩, heB, ?_⟩
  intro t ht
  by_contra hn
  have htlow : ‖β t‖ ≤ B := le_of_not_gt hn
  have hct : ContinuousOn (fun s => ‖β s‖) (Icc t T) :=
    hβ.norm.mono (Icc_subset_Icc_left (htB.1.1.trans ht.1.le))
  obtain ⟨s, hs, hse⟩ := intermediate_value_Icc ht.2 hct ⟨htlow, hBT.le⟩
  have hsK : s ∈ K := ⟨⟨htB.1.1.trans (ht.1.le.trans hs.1), hs.2⟩, hse⟩
  exact (not_le_of_gt (ht.1.trans_le hs.1)) (hmax hsK)

def connectorTop (B x : ℝ) : ℂ := (x : ℂ) + (Real.sqrt (B ^ 2 - x ^ 2) : ℂ) * Complex.I

def verticalConnector (B x : ℝ) : Set ℂ :=
  {z | z.re = x ∧ B / 4 ≤ z.im ∧ z.im ≤ Real.sqrt (B ^ 2 - x ^ 2)}

def initialRectangle (B : ℝ) : Set ℂ :=
  {z | |z.re| < B / 16 ∧ 0 ≤ z.im ∧ z.im ≤ B / 4}

lemma circle_height_pos {B x : ℝ} (hB : 0 < B) (hx : |x| < B / 16) :
    0 < B ^ 2 - x ^ 2 := by
  have hs : x ^ 2 < (B / 16) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg x) (by positivity)).mpr hx
  nlinarith

lemma connectorTop_norm {B x : ℝ} (hB : 0 < B) (hx : |x| < B / 16) :
    ‖connectorTop B x‖ = B := by
  have hs := Real.sq_sqrt (circle_height_pos hB hx).le
  have hn := Complex.sq_norm (connectorTop B x)
  simp [connectorTop, Complex.normSq_apply] at hn
  change ‖connectorTop B x‖ ^ 2 = x * x +
    Real.sqrt (B ^ 2 - x ^ 2) * Real.sqrt (B ^ 2 - x ^ 2) at hn
  nlinarith [norm_nonneg (connectorTop B x)]

/-- The entire vertical connector lies in the central sector controlled by
the small-image estimate, including its lower endpoint. -/
theorem verticalConnector_subset_sector {B x : ℝ}
    (hB : 0 < B) (hx : |x| < B / 16) :
    verticalConnector B x ⊆
      {z | B / 8 ≤ ‖z‖ ∧ ‖z‖ ≤ B ∧ ‖z‖ / 2 ≤ z.im} := by
  intro z hz
  obtain ⟨hzx, hzlow, hzup⟩ := hz
  have hs := Real.sq_sqrt (circle_height_pos hB hx).le
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply, hzx] at hn
  have hzpos : 0 < z.im := (by positivity : 0 < B / 4).trans_le hzlow
  have hsx : x ^ 2 < (B / 16) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg x) (by positivity)).mpr hx
  have hsy : z.im ^ 2 ≤ (Real.sqrt (B ^ 2 - x ^ 2)) ^ 2 :=
    (sq_le_sq₀ hzpos.le (Real.sqrt_nonneg _)).mpr hzup
  have hly : (B / 4) ^ 2 ≤ z.im ^ 2 :=
    (sq_le_sq₀ (by positivity) hzpos.le).mpr hzlow
  have hnim : z.im ≤ ‖z‖ := Complex.im_le_norm z
  refine ⟨by linarith, ?_, ?_⟩
  · nlinarith [norm_nonneg z]
  · nlinarith [norm_nonneg z]

lemma initialRectangle_subset_smallBall {B : ℝ} (hB : 0 < B) :
    initialRectangle B ⊆ ball (0 : ℂ) (B / 2) := by
  intro z hz
  obtain ⟨hxr, hy0, hyr⟩ := hz
  have hsx : z.re ^ 2 < (B / 16) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mpr hxr
  have hsy : z.im ^ 2 ≤ (B / 4) ^ 2 := (sq_le_sq₀ hy0 (by positivity)).mpr hyr
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply] at hn
  rw [mem_ball_zero_iff]
  nlinarith [norm_nonneg z]

/-- Above its first point, the vertical connector is disjoint from every
initial hull contained in the specified rectangle. -/
lemma verticalConnector_meets_rectangle_only_at_start {B x : ℝ}
    {z : ℂ} (hz : z ∈ verticalConnector B x) (hrect : z ∈ initialRectangle B) :
    z = (x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simpa using hz.1
  · simpa using le_antisymm hrect.2.2 hz.2.1

lemma circle_and_outerGuide_avoid_initialRectangle {B : ℝ} (hB : 0 < B)
    {z : ℂ} (hz : B ≤ ‖z‖) : z ∉ initialRectangle B := by
  intro hrect
  have hh := mem_ball_zero_iff.mp (initialRectangle_subset_smallBall hB hrect)
  linarith

def semicircleArc (B α ω : ℝ) : Set ℂ :=
  (fun θ : ℝ => (B : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) '' uIcc α ω

lemma semicircleArc_compact (B α ω : ℝ) : IsCompact (semicircleArc B α ω) := by
  apply isCompact_uIcc.image
  exact continuous_const.mul ((Complex.continuous_ofReal.mul continuous_const).cexp)

lemma semicircleArc_norm {B α ω : ℝ} (hB : 0 < B) {z : ℂ}
    (hz : z ∈ semicircleArc B α ω) : ‖z‖ = B := by
  obtain ⟨θ, _, rfl⟩ := hz
  simp [Complex.norm_real, abs_of_pos hB, Complex.norm_exp]

lemma semicircleArc_subset_halfPlane {B α ω : ℝ} (hB : 0 < B)
    (hα : α ∈ Ioo 0 Real.pi) (hω : ω ∈ Ioo 0 Real.pi) :
    semicircleArc B α ω ⊆ {z : ℂ | 0 < z.im} := by
  rintro z ⟨θ, hθ, rfl⟩
  have hθ' := ordConnected_Ioo.uIcc_subset hα hω hθ
  change 0 < ((B : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im
  simpa [Complex.exp_im] using mul_pos hB (Real.sin_pos_of_pos_of_lt_pi hθ'.1 hθ'.2)

lemma verticalConnector_eq_image (B x : ℝ) : verticalConnector B x =
    (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) ''
      Icc (B / 4) (Real.sqrt (B ^ 2 - x ^ 2)) := by
  ext z
  constructor
  · rintro ⟨hx, hlo, hup⟩
    refine ⟨z.im, ⟨hlo, hup⟩, ?_⟩
    apply Complex.ext <;> simp [← hx]
  · rintro ⟨y, hy, rfl⟩
    simpa [verticalConnector] using And.intro (rfl : x = x) hy

lemma verticalConnector_compact (B x : ℝ) : IsCompact (verticalConnector B x) := by
  rw [verticalConnector_eq_image]
  apply isCompact_Icc.image
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

lemma verticalConnector_subset_halfPlane {B x : ℝ} (hB : 0 < B) :
    verticalConnector B x ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  exact lt_of_lt_of_le (by positivity : 0 < B / 4) hz.2.1

/-- The actual compact set traced by the vertical piece, the circular piece,
and the remainder of the guide. -/
def continuationRoute (B x α ω : ℝ) (β : ℝ → ℂ) (tB T : ℝ) : Set ℂ :=
  verticalConnector B x ∪ semicircleArc B α ω ∪ β '' Icc tB T

theorem continuationRoute_compact
    {B x α ω tB T : ℝ} {β : ℝ → ℂ}
    (hβ : ContinuousOn β (Icc 0 T)) (htB : 0 ≤ tB) :
    IsCompact (continuationRoute B x α ω β tB T) := by
  exact ((verticalConnector_compact B x).union (semicircleArc_compact B α ω)).union
    (isCompact_Icc.image_of_continuousOn (hβ.mono (Icc_subset_Icc_left htB)))

theorem continuationRoute_subset_halfPlane
    {B x α ω tB T : ℝ} {β : ℝ → ℂ} (hB : 0 < B)
    (hα : α ∈ Ioo 0 Real.pi) (hω : ω ∈ Ioo 0 Real.pi) (htB : 0 < tB)
    (hβH : ∀ t ∈ Ioc 0 T, 0 < (β t).im) :
    continuationRoute B x α ω β tB T ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  rcases hz with (hz | hz) | ⟨t, ht, rfl⟩
  · exact verticalConnector_subset_halfPlane hB hz
  · exact semicircleArc_subset_halfPlane hB hα hω hz
  · exact hβH t ⟨htB.trans_le ht.1, ht.2⟩

/-- The continuation route avoids an arbitrary hull in the source rectangle,
except at its initial tip. -/
theorem continuationRoute_meets_rectangle_only_at_start
    {B x α ω tB T : ℝ} {β : ℝ → ℂ} (hB : 0 < B)
    (hcross : ‖β tB‖ = B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖)
    {z : ℂ} (hz : z ∈ continuationRoute B x α ω β tB T)
    (hrect : z ∈ initialRectangle B) :
    z = (x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I := by
  rcases hz with (hz | hz) | ⟨t, ht, rfl⟩
  · exact verticalConnector_meets_rectangle_only_at_start hz hrect
  · exact False.elim (circle_and_outerGuide_avoid_initialRectangle hB
      (semicircleArc_norm hB hz).ge hrect)
  · have hnorm : B ≤ ‖β t‖ := by
      rcases eq_or_lt_of_le ht.1 with he | he
      · simpa only [← he, hcross] using (le_rfl : B ≤ B)
      · exact (hafter t ⟨he, ht.2⟩).le
    exact False.elim (circle_and_outerGuide_avoid_initialRectangle hB hnorm hrect)

/-- The vertical connector reaches the radius-`B` circle only at its top. -/
lemma verticalConnector_meets_circle_only_at_top {B x : ℝ}
    (hB : 0 < B) (hx : |x| < B / 16) {z : ℂ}
    (hz : z ∈ verticalConnector B x) (hcircle : ‖z‖ = B) :
    z = connectorTop B x := by
  have hs := Real.sq_sqrt (circle_height_pos hB hx).le
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply, hz.1, hcircle] at hn
  have hzim : 0 < z.im := (by positivity : 0 < B / 4).trans_le hz.2.1
  apply Complex.ext
  · simpa [connectorTop] using hz.1
  · simp only [connectorTop, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    nlinarith [Real.sqrt_nonneg (B ^ 2 - x ^ 2)]

/-- The tail meets the selected circle only at the last-crossing point. -/
lemma tail_meets_circle_only_at_start {β : ℝ → ℂ} {B tB T : ℝ}
    (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖) {z : ℂ}
    (hz : z ∈ β '' Icc tB T) (hcircle : ‖z‖ = B) : z = β tB := by
  obtain ⟨t, ht, rfl⟩ := hz
  rcases eq_or_lt_of_le ht.1 with he | he
  · rw [← he]
  · exact False.elim ((ne_of_gt (hafter t ⟨he, ht.2⟩)) hcircle)

lemma verticalConnector_inter_semicircleArc {B x α ω : ℝ}
    (hB : 0 < B) (hx : |x| < B / 16) :
    verticalConnector B x ∩ semicircleArc B α ω ⊆ {connectorTop B x} := by
  intro z hz
  exact verticalConnector_meets_circle_only_at_top hB hx hz.1 (semicircleArc_norm hB hz.2)

lemma semicircleArc_inter_tail {β : ℝ → ℂ} {B α ω tB T : ℝ}
    (hB : 0 < B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖) :
    semicircleArc B α ω ∩ β '' Icc tB T ⊆ {β tB} := by
  intro z hz
  exact tail_meets_circle_only_at_start hafter hz.2 (semicircleArc_norm hB hz.1)

lemma verticalConnector_inter_tail {β : ℝ → ℂ} {B x tB T : ℝ}
    (hB : 0 < B) (hx : |x| < B / 16)
    (hcross : ‖β tB‖ = B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖) :
    verticalConnector B x ∩ β '' Icc tB T ⊆ {connectorTop B x} ∩ {β tB} := by
  rintro z ⟨hz, t, ht, rfl⟩
  have hle := (verticalConnector_subset_sector hB hx hz).2.1
  have hteq : tB = t := by
    rcases eq_or_lt_of_le ht.1 with he | he
    · exact he
    · exact False.elim (not_lt_of_ge hle (hafter t ⟨he, ht.2⟩))
  have hcircle : ‖β t‖ = B := by rwa [← hteq]
  exact ⟨verticalConnector_meets_circle_only_at_top hB hx hz hcircle, by simp [← hteq]⟩

lemma path_trans_injective {x y z : ℂ} {p : Path x y} {q : Path y z}
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ s t : unitInterval, p s = q t → s = 1 ∧ t = 0) :
    Function.Injective (p.trans q) := by
  intro s t he
  apply Subtype.ext
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [Path.trans_apply, dite_eq_left hs, dite_eq_left ht] at he
      have hv := congrArg (fun v : unitInterval => (v : ℝ)) (hp he)
      dsimp only at hv
      linarith
    · simp only [Path.trans_apply, dite_eq_left hs, dite_eq_right ht] at he
      obtain ⟨hv, hw⟩ := hmeet _ _ he
      have hv' := congrArg (fun v : unitInterval => (v : ℝ)) hv
      have hw' := congrArg (fun v : unitInterval => (v : ℝ)) hw
      change 2 * (s : ℝ) = 1 at hv'
      change 2 * (t : ℝ) - 1 = 0 at hw'
      linarith
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [Path.trans_apply, dite_eq_right hs, dite_eq_left ht] at he
      obtain ⟨hv, hw⟩ := hmeet _ _ he.symm
      have hv' := congrArg (fun v : unitInterval => (v : ℝ)) hv
      have hw' := congrArg (fun v : unitInterval => (v : ℝ)) hw
      change 2 * (t : ℝ) = 1 at hv'
      change 2 * (s : ℝ) - 1 = 0 at hw'
      linarith
    · simp only [Path.trans_apply, dite_eq_right hs, dite_eq_right ht] at he
      have hv := congrArg (fun v : unitInterval => (v : ℝ)) (hq he)
      dsimp only at hv
      linarith

def circlePoint (B θ : ℝ) : ℂ := (B : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

def circularPath (B α ω : ℝ) : Path (circlePoint B α) (circlePoint B ω) :=
  (Path.segment α ω).map
    (show Continuous (circlePoint B) from
      continuous_const.mul ((Complex.continuous_ofReal.mul continuous_const).cexp))

lemma circularPath_range (B α ω : ℝ) :
    range (circularPath B α ω) = semicircleArc B α ω := by
  rw [circularPath, Path.map_coe, range_comp, Path.range_segment, segment_eq_uIcc]
  rfl

lemma circularPath_injective {B α ω : ℝ} (hB : 0 < B)
    (hα : α ∈ Ioo 0 Real.pi) (hω : ω ∈ Ioo 0 Real.pi) (hne : α ≠ ω) :
    Function.Injective (circularPath B α ω) := by
  intro s t he
  have hs : (Path.segment α ω) s ∈ Ioo 0 Real.pi :=
    ordConnected_Ioo.uIcc_subset hα hω (by
      rw [← segment_eq_uIcc, ← Path.range_segment]; exact mem_range_self s)
  have ht : (Path.segment α ω) t ∈ Ioo 0 Real.pi :=
    ordConnected_Ioo.uIcc_subset hα hω (by
      rw [← segment_eq_uIcc, ← Path.range_segment]; exact mem_range_self t)
  change circlePoint B ((Path.segment α ω) s) = circlePoint B ((Path.segment α ω) t) at he
  have heexp := mul_left_cancel₀ (show (B : ℂ) ≠ 0 by exact_mod_cast hB.ne') he
  have hearg := exp_injective_strip
    (SmallImageSemicircle.stripPoint_mem (v := 0) hs)
    (SmallImageSemicircle.stripPoint_mem (v := 0) ht)
    (by simpa only [SmallImageSemicircle.stripPoint, Complex.ofReal_zero, zero_add] using heexp)
  have hangle := congrArg Complex.im hearg
  simp only [SmallImageSemicircle.stripPoint, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add] at hangle
  exact Path.segment_injective_of_ne hne hangle

lemma path_trans_injective_of_inter {x y z : ℂ} {p : Path x y} {q : Path y z}
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : range p ∩ range q ⊆ {y}) : Function.Injective (p.trans q) := by
  apply path_trans_injective hp hq
  intro s t he
  have hy : p s = y := hmeet ⟨mem_range_self s, ⟨t, he.symm⟩⟩
  exact ⟨hp (hy.trans p.target.symm), hq ((he.symm.trans hy).trans q.source.symm)⟩

lemma circle_height_gt_quarter {B x : ℝ} (hB : 0 < B) (hx : |x| < B / 16) :
    B / 4 < Real.sqrt (B ^ 2 - x ^ 2) := by
  have hs := Real.sq_sqrt (circle_height_pos hB hx).le
  have hsx : x ^ 2 < (B / 16) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg x) (by positivity)).mpr hx
  nlinarith [Real.sqrt_nonneg (B ^ 2 - x ^ 2)]

def verticalPath (B x : ℝ) :
    Path ((x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I) (connectorTop B x) :=
  (Path.segment (B / 4) (Real.sqrt (B ^ 2 - x ^ 2))).map
    (f := fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I)
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

lemma verticalPath_range {B x : ℝ} (hB : 0 < B) (hx : |x| < B / 16) :
    range (verticalPath B x) = verticalConnector B x := by
  change range ((fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) ∘
    (Path.segment (B / 4) (Real.sqrt (B ^ 2 - x ^ 2)))) = _
  rw [range_comp, Path.range_segment,
    segment_eq_Icc (circle_height_gt_quarter hB hx).le, verticalConnector_eq_image]

lemma verticalPath_injective {B x : ℝ} (hB : 0 < B) (hx : |x| < B / 16) :
    Function.Injective (verticalPath B x) := by
  intro s t he
  have hh := congrArg Complex.im he
  change ((x : ℂ) + ((Path.segment (B / 4) (Real.sqrt (B ^ 2 - x ^ 2))) s : ℂ) * Complex.I).im =
    ((x : ℂ) + ((Path.segment (B / 4) (Real.sqrt (B ^ 2 - x ^ 2))) t : ℂ) * Complex.I).im at hh
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hh
  exact Path.segment_injective_of_ne (ne_of_lt (circle_height_gt_quarter hB hx)) hh

def tailPath {β : ℝ → ℂ} {tB T : ℝ} (ht : tB ≤ T)
    (hβ : ContinuousOn β (Icc tB T)) : Path (β tB) (β T) :=
  (Path.segment tB T).map' (f := β) (by
    rw [Path.range_segment, segment_eq_Icc ht]
    exact hβ)

lemma tailPath_range {β : ℝ → ℂ} {tB T : ℝ} (ht : tB ≤ T)
    (hβ : ContinuousOn β (Icc tB T)) : range (tailPath ht hβ) = β '' Icc tB T := by
  change range (β ∘ Path.segment tB T) = _
  rw [range_comp, Path.range_segment, segment_eq_Icc ht]

lemma tailPath_injective {β : ℝ → ℂ} {tB T : ℝ} (ht : tB < T)
    (hβ : ContinuousOn β (Icc tB T)) (hi : InjOn β (Icc tB T)) :
    Function.Injective (tailPath ht.le hβ) := by
  intro s t he
  change β ((Path.segment tB T) s) = β ((Path.segment tB T) t) at he
  have hs : (Path.segment tB T) s ∈ Icc tB T := by
    rw [← segment_eq_Icc ht.le, ← Path.range_segment]; exact mem_range_self s
  have ht' : (Path.segment tB T) t ∈ Icc tB T := by
    rw [← segment_eq_Icc ht.le, ← Path.range_segment]; exact mem_range_self t
  exact Path.segment_injective_of_ne ht.ne (hi hs ht' he)

/-- The three source pieces form an actual simple continuation path. When
the circular arc degenerates, it is omitted from the parametrization. -/
theorem exists_simple_continuation_path
    {B x α ω tB T : ℝ} {β : ℝ → ℂ}
    (hB : 0 < B) (hx : |x| < B / 16)
    (hα : α ∈ Ioo 0 Real.pi) (hω : ω ∈ Ioo 0 Real.pi)
    (htB : tB < T) (hβ : ContinuousOn β (Icc tB T)) (hi : InjOn β (Icc tB T))
    (hstart : connectorTop B x = circlePoint B α) (hend : β tB = circlePoint B ω)
    (hcross : ‖β tB‖ = B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖) :
    ∃ p : Path ((x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I) (β T),
      Function.Injective p ∧ range p = continuationRoute B x α ω β tB T := by
  let v := verticalPath B x
  let q := tailPath htB.le hβ
  have hv : Function.Injective v := verticalPath_injective hB hx
  have hq : Function.Injective q := tailPath_injective htB hβ hi
  have hvr : range v = verticalConnector B x := verticalPath_range hB hx
  have hqr : range q = β '' Icc tB T := tailPath_range htB.le hβ
  by_cases heq : α = ω
  · have htop : connectorTop B x = β tB :=
      hstart.trans ((congrArg (circlePoint B) heq).trans hend.symm)
    let v' := v.cast rfl htop.symm
    have hv' : Function.Injective v' := hv
    have hvr' : range v' = verticalConnector B x := hvr
    have hmeet : range v' ∩ range q ⊆ {β tB} := by
      rw [hvr', hqr]
      exact (verticalConnector_inter_tail hB hx hcross hafter).trans inter_subset_right
    refine ⟨v'.trans q, path_trans_injective_of_inter hv' hq hmeet, ?_⟩
    have hArc : semicircleArc B α ω ⊆ verticalConnector B x := by
      intro z hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      have hθα : θ = α := by simpa only [← heq, uIcc_self, mem_singleton_iff] using hθ
      rw [hθα]
      change circlePoint B α ∈ verticalConnector B x
      rw [← hstart, ← hvr]
      exact ⟨1, v.target⟩
    rw [Path.trans_range, hvr', hqr]
    unfold continuationRoute
    rw [union_eq_left.mpr hArc]
  · let c := (circularPath B α ω).cast hstart hend
    have hc : Function.Injective c := circularPath_injective hB hα hω heq
    have hcr : range c = semicircleArc B α ω := circularPath_range B α ω
    have hmeet : range v ∩ range c ⊆ {connectorTop B x} := by
      rw [hvr, hcr]
      exact verticalConnector_inter_semicircleArc hB hx
    have hvc : Function.Injective (v.trans c) := path_trans_injective_of_inter hv hc hmeet
    have hmeetq : range (v.trans c) ∩ range q ⊆ {β tB} := by
      rw [Path.trans_range, hvr, hcr, hqr]
      rintro z ⟨hz | hz, hzt⟩
      · exact (verticalConnector_inter_tail hB hx hcross hafter ⟨hz, hzt⟩).2
      · exact semicircleArc_inter_tail hB hafter ⟨hz, hzt⟩
    refine ⟨(v.trans c).trans q, path_trans_injective_of_inter hvc hq hmeetq, ?_⟩
    rw [Path.trans_range, Path.trans_range, hvr, hcr, hqr]
    rfl

lemma arg_mem_upper_interval {z : ℂ} (hz : 0 < z.im) : z.arg ∈ Ioo 0 Real.pi := by
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) ?_,
    Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')⟩
  intro heq
  exact hz.ne' (Complex.arg_eq_zero_iff.mp heq.symm).2

/-- The source splice as an injective path in a compact subset of the upper
half-plane. It meets any initial hull in the prescribed rectangle only at
the starting tip. -/
theorem exists_simple_splice_path
    {B x tB T : ℝ} {β : ℝ → ℂ} (hB : 0 < B) (hx : |x| < B / 16)
    (htB₀ : 0 < tB) (htBT : tB < T)
    (hβ : ContinuousOn β (Icc 0 T)) (hi : InjOn β (Icc 0 T))
    (hβH : ∀ t ∈ Ioc 0 T, 0 < (β t).im)
    (hcross : ‖β tB‖ = B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖) :
    ∃ p : Path ((x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I) (β T),
      Function.Injective p ∧ IsCompact (range p) ∧
      range p ⊆ {z : ℂ | 0 < z.im} ∧
      (∀ z ∈ range p, z ∈ initialRectangle B →
        z = (x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I) ∧
      range p = continuationRoute B x (connectorTop B x).arg (β tB).arg β tB T := by
  have htopH : 0 < (connectorTop B x).im := by
    simpa [connectorTop] using Real.sqrt_pos.mpr (circle_height_pos hB hx)
  have htH := hβH tB ⟨htB₀, htBT.le⟩
  have hα := arg_mem_upper_interval htopH
  have hω := arg_mem_upper_interval htH
  have hstart : connectorTop B x = circlePoint B (connectorTop B x).arg := by
    calc
      _ = (‖connectorTop B x‖ : ℂ) * Complex.exp (((connectorTop B x).arg : ℂ) * Complex.I) :=
        (Complex.norm_mul_exp_arg_mul_I _).symm
      _ = _ := by rw [connectorTop_norm hB hx]; rfl
  have hend : β tB = circlePoint B (β tB).arg := by
    calc
      _ = (‖β tB‖ : ℂ) * Complex.exp (((β tB).arg : ℂ) * Complex.I) :=
        (Complex.norm_mul_exp_arg_mul_I _).symm
      _ = _ := by rw [hcross]; rfl
  obtain ⟨p, hp, hpr⟩ := exists_simple_continuation_path hB hx hα hω htBT
    (hβ.mono (Icc_subset_Icc_left htB₀.le)) (hi.mono (Icc_subset_Icc_left htB₀.le))
    hstart hend hcross hafter
  have hpc : IsCompact (range p) := by
    simpa only [image_univ] using isCompact_univ.image p.continuous
  refine ⟨p, hp, hpc, ?_, ?_, hpr⟩
  · rw [hpr]
    exact continuationRoute_subset_halfPlane hB hα hω htB₀ hβH
  · intro z hz hr
    exact continuationRoute_meets_rectangle_only_at_start hB hcross hafter (hpr ▸ hz) hr

end SLEExactGauge.GuideSplice

end

end OAI
