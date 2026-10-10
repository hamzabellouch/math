import OAI.Analysis.CircleDomains.Selection.ProtrusionProjection

namespace OAI

/-! Local crossing segments from a buffered anchor ball to an inner target region. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_rotatedLine (a : Circle) (y : ℝ) : Continuous (rotatedLine a y) :=
  (rotation a).continuous.comp (continuous_horizontalLine y)

theorem convex_rotatedLine_preimage (a : Circle) (y : ℝ)
    {W : Set ℂ} (hW : Convex ℝ W) : Convex ℝ (rotatedLine a y ⁻¹' W) := by
  intro p hp q hq α β hα hβ hsum
  have he : horizontalLine y (α * p + β * q) =
      α • horizontalLine y p + β • horizontalLine y q := by
    apply Complex.ext
    · simp [horizontalLine]
    · simp only [horizontalLine, Complex.add_im, Complex.real_smul, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      calc
        y = (α + β) * y := by rw [hsum, one_mul]
        _ = α * y + β * y := by ring
  change rotation a (horizontalLine y (α * p + β * q)) ∈ W
  rw [he, map_add, map_smul, map_smul]
  exact hW hp hq hα hβ hsum

theorem middle_chord_dist (a : Circle) (y : ℝ) (c : ℂ) :
    dist (rotatedLine a y ((rotation a).symm c).re) c = |y - ((rotation a).symm c).im| := by
  let d := (rotation a).symm c
  have he : horizontalLine y d.re - d = ((y - d.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [horizontalLine]
  calc
    dist (rotatedLine a y d.re) c = dist (horizontalLine y d.re) d := by
      conv_lhs => rhs; rw [← (rotation a).apply_symm_apply c]
      exact (rotation a).dist_map _ _
    _ = |y - d.im| := by
      rw [dist_eq_norm, he, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]

/-- A connected line segment joining the exterior of a closed region to its interior meets the
frontier at a parameter different from the exterior endpoint. -/
theorem exists_rotated_frontier_parameter (a : Circle) (y : ℝ)
    {U : Set ℂ} (hU : IsOpen U) {s t : ℝ}
    (hs : rotatedLine a y s ∉ closure U) (ht : rotatedLine a y t ∈ U) :
    ∃ b ∈ uIcc s t, b ≠ s ∧ rotatedLine a y b ∈ frontier U := by
  let C := rotatedLine a y '' uIcc s t
  have hC : IsPreconnected C :=
    isPreconnected_uIcc.image _ (continuous_rotatedLine a y).continuousOn
  have hsC : rotatedLine a y s ∈ C := mem_image_of_mem _ left_mem_uIcc
  have htC : rotatedLine a y t ∈ C := mem_image_of_mem _ right_mem_uIcc
  have hinter : (C ∩ frontier U).Nonempty := by
    by_contra h
    have havoid : ∀ z ∈ C, z ∉ frontier U := by
      intro z hz hzF
      exact h ⟨z, hz, hzF⟩
    have hcover : C ⊆ U ∪ (closure U)ᶜ := by
      intro z hz
      by_cases hzU : z ∈ U
      · exact Or.inl hzU
      · right
        intro hzcl
        exact havoid z hz ⟨hzcl, by simpa only [hU.interior_eq] using hzU⟩
    have hd : Disjoint U (closure U)ᶜ := disjoint_left.mpr
      (fun z hz hzc => hzc (subset_closure hz))
    rcases hC.subset_or_subset hU isClosed_closure.isOpen_compl hd hcover with h | h
    · exact hs (subset_closure (h hsC))
    · exact h htC (subset_closure ht)
  obtain ⟨z, ⟨b, hb, rfl⟩, hbf⟩ := hinter
  refine ⟨b, hb, ?_, hbf⟩
  intro he
  subst b
  exact hs hbf.1

/-- The compact transverse overlap supplies local segments starting strictly in the anchor ball
and ending on the inner frontier. The entire paid segment stays in the chosen convex region. -/
theorem localized_frontier_crossings (a : Circle)
    {U Q W : Set ℂ} (hU : IsOpen U) (hQU : Q ⊆ U) (hQW : Q ⊆ W)
    (hW : Convex ℝ W) {c : ℂ} {δ : ℝ}
    (hball : ball c δ ⊆ (closure U)ᶜ ∩ W) {J : Set ℝ}
    (hJ : J ⊆ (fun z => ((rotation a).symm z).im) '' Q ∩
      Ioo (((rotation a).symm c).im - δ) (((rotation a).symm c).im + δ)) :
    ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      rotatedLine a y s ∈ ball c δ ∧ rotatedLine a y t ∈ frontier U ∧
      ∀ x ∈ uIcc s t, rotatedLine a y x ∈ W := by
  intro y hy
  obtain ⟨⟨q, hq, hqy⟩, hyl, hyr⟩ := hJ hy
  let s := ((rotation a).symm c).re
  let t := ((rotation a).symm q).re
  have hsball : rotatedLine a y s ∈ ball c δ := by
    rw [mem_ball, middle_chord_dist]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hqt : rotatedLine a y t = q := by
    change rotation a (horizontalLine y ((rotation a).symm q).re) = q
    rw [show horizontalLine y ((rotation a).symm q).re = (rotation a).symm q by
      apply Complex.ext
      · rfl
      · exact hqy.symm]
    exact (rotation a).apply_symm_apply q
  obtain ⟨b, hb, hbs, hbf⟩ := exists_rotated_frontier_parameter a y hU
    (hball hsball).1 (hqt ▸ hQU hq)
  have hsegment : uIcc s t ⊆ rotatedLine a y ⁻¹' W :=
    (convex_rotatedLine_preimage a y hW).ordConnected.uIcc_subset
      (hball hsball).2 (by change rotatedLine a y t ∈ W; simpa only [hqt] using hQW hq)
  exact ⟨s, b, hbs.symm, hsball, hbf, (uIcc_subset_uIcc_left hb).trans hsegment⟩

end CircleDomainRigidity

end

end OAI
