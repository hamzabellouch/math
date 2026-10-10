import OAI.Probability.SLE.Geometry.PublishedPlanarDiskOpenness

namespace OAI

/-! Opposite local sides of a straightened crosscut.  This is a deterministic
consequence of disk-image openness and the intermediate value theorem.  It
does not assume any classification of ribbon exits or harmonic measures. -/

noncomputable section
open Set Metric
open scoped Topology

namespace SLEExactGauge.CrosscutSides

theorem positive_on_preconnected_of_nonzero
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    {f : X → ℝ} (hf : ContinuousOn f S) (hn : ∀ z ∈ S, f z ≠ 0)
    {a : X} (ha : a ∈ S) (hfa : 0 < f a) : ∀ z ∈ S, 0 < f z := by
  intro z hz
  by_contra hh
  have hzneg : f z < 0 := lt_of_le_of_ne (le_of_not_gt hh) (hn z hz)
  obtain ⟨w, hw, he⟩ := hS.intermediate_value hz ha hf ⟨hzneg.le, hfa.le⟩
  exact hn w hw he

theorem negative_on_preconnected_of_nonzero
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    {f : X → ℝ} (hf : ContinuousOn f S) (hn : ∀ z ∈ S, f z ≠ 0)
    {a : X} (ha : a ∈ S) (hfa : f a < 0) : ∀ z ∈ S, f z < 0 := by
  have hh := positive_on_preconnected_of_nonzero hS hf.neg
    (fun z hz => neg_ne_zero.mpr (hn z hz)) ha (neg_pos.mpr hfa)
  intro z hz
  exact neg_pos.mp (hh z hz)

/-- An open image of a disk cannot send both sides of its horizontal
diameter into the same side of the vertical axis.  The zero-set assumption
is exactly the assertion that this diameter is the local crosscut. -/
theorem opposite_half_disk_signs
    (f : ℂ → ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (ball x r)) (ho : IsOpen (f '' ball x r))
    (hfx : (f x).re = 0)
    (hz : ∀ z ∈ ball x r, (f z).re = 0 ↔ z.im = 0) :
    ((∀ z ∈ ball x r, 0 < z.im → 0 < (f z).re) ∧
      (∀ z ∈ ball x r, z.im < 0 → (f z).re < 0)) ∨
    ((∀ z ∈ ball x r, 0 < z.im → (f z).re < 0) ∧
      (∀ z ∈ ball x r, z.im < 0 → 0 < (f z).re)) := by
  let U := ball x r ∩ {z : ℂ | 0 < z.im}
  let V := ball x r ∩ {z : ℂ | z.im < 0}
  have hU : IsPreconnected U :=
    ((convex_ball x r : Convex ℝ (ball x r)).inter
      (convex_halfSpace_gt Complex.imLm.isLinear 0)).isPreconnected
  have hV : IsPreconnected V :=
    ((convex_ball x r : Convex ℝ (ball x r)).inter
      (convex_halfSpace_lt Complex.imLm.isLinear 0)).isPreconnected
  have hc := Complex.continuous_re.comp_continuousOn hf
  have hnU : ∀ z ∈ U, (f z).re ≠ 0 :=
    fun z hz' he => (ne_of_gt hz'.2) ((hz z hz'.1).mp he)
  have hnV : ∀ z ∈ V, (f z).re ≠ 0 :=
    fun z hz' he => (ne_of_lt hz'.2) ((hz z hz'.1).mp he)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp ho (f x)
    (mem_image_of_mem f (mem_ball_self hr))
  have hplus : f x + (δ / 2 : ℝ) ∈ ball (f x) δ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < δ / 2)]
    linarith
  have hminus : f x - (δ / 2 : ℝ) ∈ ball (f x) δ := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < δ / 2)]
    linarith
  obtain ⟨a, ha, hea⟩ := hδsub hplus
  obtain ⟨b, hb, heb⟩ := hδsub hminus
  have hapos : 0 < (f a).re := by rw [hea, Complex.add_re, Complex.ofReal_re, hfx]; positivity
  have hbneg : (f b).re < 0 := by rw [heb, Complex.sub_re, Complex.ofReal_re, hfx]; linarith
  have hai : a.im ≠ 0 := fun he => (ne_of_gt hapos) ((hz a ha).mpr he)
  have hbi : b.im ≠ 0 := fun he => (ne_of_lt hbneg) ((hz b hb).mpr he)
  rcases lt_or_gt_of_ne hai with han | hap
  · have hVon := positive_on_preconnected_of_nonzero hV (hc.mono inter_subset_left)
      hnV ⟨ha, han⟩ hapos
    have hbp : 0 < b.im := by
      rcases lt_or_gt_of_ne hbi with hbn | hbp
      · exact False.elim ((not_lt_of_gt (hVon b ⟨hb, hbn⟩)) hbneg)
      · exact hbp
    have hUon := negative_on_preconnected_of_nonzero hU (hc.mono inter_subset_left)
      hnU ⟨hb, hbp⟩ hbneg
    exact Or.inr ⟨fun z hz' hi => hUon z ⟨hz', hi⟩,
      fun z hz' hi => hVon z ⟨hz', hi⟩⟩
  · have hUon := positive_on_preconnected_of_nonzero hU (hc.mono inter_subset_left)
      hnU ⟨ha, hap⟩ hapos
    have hbn : b.im < 0 := by
      rcases lt_or_gt_of_ne hbi with hbn | hbp
      · exact hbn
      · exact False.elim ((not_lt_of_gt (hUon b ⟨hb, hbp⟩)) hbneg)
    have hVon := negative_on_preconnected_of_nonzero hV (hc.mono inter_subset_left)
      hnV ⟨hb, hbn⟩ hbneg
    exact Or.inl ⟨fun z hz' hi => hUon z ⟨hz', hi⟩,
      fun z hz' hi => hVon z ⟨hz', hi⟩⟩

end SLEExactGauge.CrosscutSides

end

end OAI
