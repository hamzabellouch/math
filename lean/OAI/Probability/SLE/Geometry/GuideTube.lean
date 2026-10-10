import OAI.Probability.SLE.Geometry.GuideSplice
import OAI.Probability.SLE.Gauge.ConformalCompactSausage

namespace OAI

/-!
Open continuation tubes for the geometric splice. The initial tip is a
boundary point of the tube; every positive-time route point lies in the tube.
This is the version compatible with avoiding the initial containing rectangle.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology unitInterval

namespace SLEExactGauge.GuideSplice

def closedInitialRectangle (B : ℝ) : Set ℂ :=
  {z | |z.re| ≤ B / 16 ∧ 0 ≤ z.im ∧ z.im ≤ B / 4}

lemma closedInitialRectangle_isClosed (B : ℝ) : IsClosed (closedInitialRectangle B) :=
  (isClosed_le Complex.continuous_re.abs continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const))

lemma initialRectangle_subset_closed (B : ℝ) :
    initialRectangle B ⊆ closedInitialRectangle B :=
  fun _ hz => ⟨hz.1.le, hz.2⟩

lemma closedInitialRectangle_subset_smallBall {B : ℝ} (hB : 0 < B) :
    closedInitialRectangle B ⊆ ball (0 : ℂ) (B / 2) := by
  intro z hz
  obtain ⟨hxr, hy0, hyr⟩ := hz
  have hsx : z.re ^ 2 ≤ (B / 16) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hxr
  have hsy : z.im ^ 2 ≤ (B / 4) ^ 2 := (sq_le_sq₀ hy0 (by positivity)).mpr hyr
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply] at hn
  rw [mem_ball_zero_iff]
  nlinarith [norm_nonneg z]

lemma outer_circle_avoids_closedInitialRectangle {B : ℝ} (hB : 0 < B)
    {z : ℂ} (hz : B ≤ ‖z‖) : z ∉ closedInitialRectangle B := by
  intro hrect
  have hh := mem_ball_zero_iff.mp (closedInitialRectangle_subset_smallBall hB hrect)
  linarith

lemma continuationRoute_meets_closed_rectangle_only_at_start
    {B x α ω tB T : ℝ} {β : ℝ → ℂ} (hB : 0 < B)
    (hcross : ‖β tB‖ = B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖)
    {z : ℂ} (hz : z ∈ continuationRoute B x α ω β tB T)
    (hrect : z ∈ closedInitialRectangle B) :
    z = (x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I := by
  rcases hz with (hz | hz) | ⟨t, ht, rfl⟩
  · apply Complex.ext
    · simpa using hz.1
    · simpa using le_antisymm hrect.2.2 hz.2.1
  · exact False.elim (outer_circle_avoids_closedInitialRectangle hB
      (semicircleArc_norm hB hz).ge hrect)
  · have hnorm : B ≤ ‖β t‖ := by
      rcases eq_or_lt_of_le ht.1 with he | he
      · simpa only [← he, hcross] using (le_rfl : B ≤ B)
      · exact (hafter t ⟨he, ht.2⟩).le
    exact False.elim (outer_circle_avoids_closedInitialRectangle hB hnorm hrect)

/-- The image bound for the actual initial vertical and circular pieces. -/
theorem initial_splice_image_subset_quarter_ball
    {F : ℂ → ℂ} {a : ℂ} {B x α ω r : ℝ}
    (hB : 0 < B) (hx : |x| < B / 16)
    (hα : α ∈ Ioo 0 Real.pi) (hω : ω ∈ Ioo 0 Real.pi)
    (hcircle : ∀ θ ∈ Ioo 0 Real.pi, ‖F (circlePoint B θ) - a‖ < r / 4)
    (hsector : ∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im →
      ‖F z - a‖ < r / 4) :
    F '' (verticalConnector B x ∪ semicircleArc B α ω) ⊆ ball a (r / 4) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_ball, dist_eq_norm]
  rcases hz with hz | ⟨θ, hθ, rfl⟩
  · obtain ⟨hlo, hup, him⟩ := verticalConnector_subset_sector hB hx hz
    exact hsector z hlo hup him
  · exact hcircle θ (ordConnected_Ioo.uIcc_subset hα hω hθ)

def continuationTube (F : ℂ → ℂ) (a : ℂ) (r B : ℝ) (O : Set ℂ) : Set ℂ :=
  (upperHalfPlane ∩ F ⁻¹' (ball a (r / 2) ∪ O)) \ closedInitialRectangle B

lemma continuationTube_isOpen {F : ℂ → ℂ} (hF : ContinuousOn F upperHalfPlane)
    (a : ℂ) (r B : ℝ) {O : Set ℂ} (hO : IsOpen O) :
    IsOpen (continuationTube F a r B O) :=
  (hF.isOpen_inter_preimage isOpen_upperHalfPlane (isOpen_ball.union hO)).sdiff
    (closedInitialRectangle_isClosed B)

lemma continuationTube_subset_halfPlane (F : ℂ → ℂ) (a : ℂ) (r B : ℝ) (O : Set ℂ) :
    continuationTube F a r B O ⊆ upperHalfPlane := fun _ hz => hz.1.1

lemma continuationTube_disjoint_rectangle (F : ℂ → ℂ) (a : ℂ) (r B : ℝ) (O : Set ℂ) :
    Disjoint (continuationTube F a r B O) (closedInitialRectangle B) :=
  disjoint_sdiff_left

lemma continuationTube_image_subset (F : ℂ → ℂ) (a : ℂ) (r B : ℝ) (O : Set ℂ) :
    F '' continuationTube F a r B O ⊆ ball a (r / 2) ∪ O := by
  rintro _ ⟨z, hz, rfl⟩
  exact hz.1.2

/-- An open tube avoids the entire initial rectangle while retaining every
continuation point other than the initial tip. Its physical image lies in the
half-radius ball or in the prescribed open region for the compact tail. -/
theorem continuationRoute_rest_subset_tube
    {F : ℂ → ℂ} {a : ℂ} {B x α ω r tB T : ℝ} {β : ℝ → ℂ} {O : Set ℂ}
    (hr : 0 < r) (hB : 0 < B) (hx : |x| < B / 16)
    (hα : α ∈ Ioo 0 Real.pi) (hω : ω ∈ Ioo 0 Real.pi) (htB : 0 < tB)
    (hβH : ∀ t ∈ Ioc 0 T, 0 < (β t).im)
    (hcross : ‖β tB‖ = B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖)
    (hcircle : ∀ θ ∈ Ioo 0 Real.pi, ‖F (circlePoint B θ) - a‖ < r / 4)
    (hsector : ∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im →
      ‖F z - a‖ < r / 4)
    (htail : F '' (β '' Icc tB T) ⊆ O) :
    continuationRoute B x α ω β tB T \
        {(x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I} ⊆ continuationTube F a r B O := by
  intro z hz
  refine ⟨⟨continuationRoute_subset_halfPlane hB hα hω htB hβH hz.1, ?_⟩, ?_⟩
  · rcases hz.1 with (hz | hz) | hz
    · left
      have hh := initial_splice_image_subset_quarter_ball hB hx hα hω hcircle hsector
        (mem_image_of_mem F (Or.inl hz))
      exact ball_subset_ball (by linarith) hh
    · left
      have hh := initial_splice_image_subset_quarter_ball hB hx hα hω hcircle hsector
        (mem_image_of_mem F (Or.inr hz))
      exact ball_subset_ball (by linarith) hh
    · exact Or.inr (htail (mem_image_of_mem F hz))
  · intro hrect
    exact hz.2 (continuationRoute_meets_closed_rectangle_only_at_start hB hcross hafter hz.1 hrect)

lemma initial_tip_mem_closure_of_connector_rest
    {B x : ℝ} (hB : 0 < B) (hx : |x| < B / 16) {N : Set ℂ}
    (hsub : verticalConnector B x \
      {(x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I} ⊆ N) :
    (x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I ∈ closure N := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let d := min (ε / 2) ((Real.sqrt (B ^ 2 - x ^ 2) - B / 4) / 2)
  have hd : 0 < d := lt_min (by positivity) (by
    have hh := circle_height_gt_quarter hB hx
    positivity)
  let z : ℂ := (x : ℂ) + (((B / 4 + d : ℝ)) : ℂ) * Complex.I
  have hzV : z ∈ verticalConnector B x := by
    have hu := min_le_right (ε / 2) ((Real.sqrt (B ^ 2 - x ^ 2) - B / 4) / 2)
    simp only [z, verticalConnector, mem_ofPred_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, sub_self, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add]
    dsimp only [d] at hd
    exact ⟨trivial, by dsimp only [d]; linarith, by dsimp only [d]; linarith⟩
  have hzne : z ≠ (x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I := by
    intro he
    have hh := congrArg Complex.im he
    simp [z] at hh
    exact hd.ne' hh
  refine ⟨z, hsub ⟨hzV, hzne⟩, ?_⟩
  have hdε : d < ε := (min_le_left _ _).trans_lt (by linarith)
  have he : z - ((x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I) = (d : ℂ) * Complex.I := by
    dsimp only [z]
    push_cast
    ring
  rw [dist_comm, dist_eq_norm, he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hd, Complex.norm_I, mul_one]
  exact hdε

lemma initial_tip_mem_closure_of_route_rest
    {B x α ω tB T : ℝ} {β : ℝ → ℂ} (hB : 0 < B) (hx : |x| < B / 16)
    {N : Set ℂ} (hsub : continuationRoute B x α ω β tB T \
      {(x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I} ⊆ N) :
    (x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I ∈ closure N :=
  initial_tip_mem_closure_of_connector_rest hB hx
    (fun _ hz => hsub ⟨Or.inl (Or.inl hz.1), hz.2⟩)

/-- Compact parts of the initial splice have a tube lying entirely in the
physical half-radius ball, as well as outside the old containing rectangle. -/
theorem compact_initial_splice_has_small_image_tube
    {F : ℂ → ℂ} (hF : ContinuousOn F upperHalfPlane) {a : ℂ}
    {B x α ω r : ℝ} (hr : 0 < r) (hB : 0 < B) (hx : |x| < B / 16)
    (hα : α ∈ Ioo 0 Real.pi) (hω : ω ∈ Ioo 0 Real.pi)
    (hcircle : ∀ θ ∈ Ioo 0 Real.pi, ‖F (circlePoint B θ) - a‖ < r / 4)
    (hsector : ∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im →
      ‖F z - a‖ < r / 4)
    (K : Set ℂ) (hK : IsCompact K)
    (hsub : K ⊆ (verticalConnector B x ∪ semicircleArc B α ω) \
      {(x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I}) :
    ∃ ε : ℝ, 0 < ε ∧ thickening ε K ⊆ continuationTube F a r B ∅ := by
  apply hK.exists_thickening_subset_open
    (continuationTube_isOpen hF a r B isOpen_empty)
  intro z hz
  have hz' := hsub hz
  refine ⟨⟨?_, Or.inl ?_⟩, ?_⟩
  · rcases hz'.1 with hv | hc
    · exact verticalConnector_subset_halfPlane hB hv
    · exact semicircleArc_subset_halfPlane hB hα hω hc
  · exact ball_subset_ball (by linarith)
      (initial_splice_image_subset_quarter_ball hB hx hα hω hcircle hsector
        (mem_image_of_mem F hz'.1))
  · intro hrect
    rcases hz'.1 with hv | hc
    · apply hz'.2
      apply Complex.ext
      · simpa using hv.1
      · simpa using le_antisymm hrect.2.2 hv.2.1
    · exact outer_circle_avoids_closedInitialRectangle hB (semicircleArc_norm hB hc).ge hrect

/-- Every compact positive-time piece of a simple route has a uniform tube
radius; the radius is allowed to shrink towards the initial tip. -/
theorem positive_subpath_has_uniform_tube
    {z₀ z₁ : ℂ} (p : Path z₀ z₁) (hp : Function.Injective p)
    {N : Set ℂ} (hN : IsOpen N) (hsub : range p \ {z₀} ⊆ N)
    (δ : unitInterval) (hδ : 0 < (δ : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ thickening ε (p '' Icc δ 1) ⊆ N := by
  apply (isCompact_Icc.image p.continuous).exists_thickening_subset_open hN
  rintro _ ⟨t, ht, rfl⟩
  apply hsub
  refine ⟨mem_range_self t, ?_⟩
  intro he
  have ht0 := hp (he.trans p.source.symm)
  have hh : (δ : ℝ) ≤ (t : ℝ) := ht.1
  have htzero : (t : ℝ) = 0 := congrArg (fun u : unitInterval => (u : ℝ)) ht0
  linarith

end SLEExactGauge.GuideSplice

end

end OAI
