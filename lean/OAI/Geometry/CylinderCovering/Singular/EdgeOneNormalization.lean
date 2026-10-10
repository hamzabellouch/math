import OAI.Geometry.CylinderCovering.Singular.EdgeOneNormalizationDefinitions
import OAI.Geometry.CylinderCovering.Rational.Normalization
import OAI.Geometry.CylinderCovering.Ruled.Similarity

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering.SingularEdgeOneCover
open RuledApproximation

lemma height_pos : 0 < height := by
  unfold height
  positivity

theorem tetrahedron_eq_centered_translation :
    tetrahedron =
      (fun z : Space => z + vec3 0 0 (height / 2)) '' SlopeRational.referenceTetrahedron := by
  ext z
  constructor
  · rintro ⟨s, hs0, hs1, hx, hy, hz⟩
    refine ⟨vec3 (z 0) (z 1) (z 2 - height / 2), ?_, ?_⟩
    · refine ⟨s - 1 / 2, by linarith, by linarith, ?_, ?_, ?_⟩
      · change |z 0| ≤ (1 / 2 + (s - 1 / 2)) / 2
        simpa only [show (1 / 2 : ℝ) + (s - 1 / 2) = s by ring] using hx
      · change |z 1| ≤ (1 / 2 - (s - 1 / 2)) / 2
        simpa only [show (1 / 2 : ℝ) - (s - 1 / 2) = 1 - s by ring] using hy
      · change z 2 - height / 2 = height * (s - 1 / 2)
        rw [hz]
        ring
    · ext i
      fin_cases i <;> simp [vec3]
  · rintro ⟨w, ⟨t, ht0, ht1, hx, hy, hz⟩, rfl⟩
    refine ⟨t + 1 / 2, by linarith, by linarith, ?_, ?_, ?_⟩
    · change |w 0 + 0| ≤ (t + 1 / 2) / 2
      simpa [add_comm] using hx
    · change |w 1 + 0| ≤ (1 - (t + 1 / 2)) / 2
      simpa only [add_zero, show (1 : ℝ) - (t + 1 / 2) = 1 / 2 - t by ring] using hy
    · change w 2 + height / 2 = height * (t + 1 / 2)
      change w 2 = height * t at hz
      rw [hz]
      ring

theorem shadowArea_eq_centered (u : Space) :
    shadowArea tetrahedron u = shadowArea SlopeRational.referenceTetrahedron u := by
  rw [tetrahedron_eq_centered_translation]
  have hmap : (fun z : Space => z + vec3 0 0 (height / 2)) =
      Similarity.map (vec3 0 0 (height / 2)) 1 (LinearIsometryEquiv.refl ℝ Space) := by
    funext z
    simp [Similarity.map, add_comm]
  rw [hmap]
  change Similarity.shadowArea
    (Similarity.map (vec3 0 0 (height / 2)) 1 (LinearIsometryEquiv.refl ℝ Space) ''
      SlopeRational.referenceTetrahedron) ((LinearIsometryEquiv.refl ℝ Space) u) = _
  rw [Similarity.shadowArea_map _ _ (by norm_num)]
  simp only [one_pow, one_mul]
  rfl

theorem tetrahedron_minimumShadowArea : minimumShadowArea tetrahedron = height / 2 := by
  have heq : minimumShadowArea tetrahedron =
      minimumShadowArea SlopeRational.referenceTetrahedron := by
    unfold minimumShadowArea
    simp only [shadowArea_eq_centered]
  rw [heq, SlopeRational.referenceTetrahedron_minimumShadowArea]
  rfl

lemma minimumShadowArea_pos : 0 < minimumShadowArea tetrahedron := by
  rw [tetrahedron_minimumShadowArea]
  exact div_pos height_pos (by norm_num)

theorem same_family_half_bounds {n m : ℕ} (C : Fin n → Cylinder)
    (D : Fin m → Cylinder) (B₁ B₂ : Cylinder)
    (hcost : familyArea C + familyArea D + B₁.area + B₂.area < height / 4) :
    familyArea C + familyArea D + B₁.area + B₂.area <
      minimumShadowArea tetrahedron / 2 ∧
    relativeCost tetrahedron C + relativeCost tetrahedron D +
      B₁.area / shadowArea tetrahedron B₁.axis +
      B₂.area / shadowArea tetrahedron B₂.axis < 1 / 2 := by
  have hmin := minimumShadowArea_pos
  have htotal : familyArea C + familyArea D + B₁.area + B₂.area <
      minimumShadowArea tetrahedron / 2 := by
    rw [tetrahedron_minimumShadowArea]
    linarith only [hcost]
  refine ⟨htotal, ?_⟩
  have hC : relativeCost tetrahedron C ≤ familyArea C / minimumShadowArea tetrahedron :=
    relativeCost_le_familyArea_div_minimum tetrahedron hmin C
  have hD : relativeCost tetrahedron D ≤ familyArea D / minimumShadowArea tetrahedron :=
    relativeCost_le_familyArea_div_minimum tetrahedron hmin D
  have hB (B : Cylinder) : B.area / shadowArea tetrahedron B.axis ≤
      B.area / minimumShadowArea tetrahedron :=
    div_le_div_of_nonneg_left ENNReal.toReal_nonneg hmin
      (Similarity.minimumArea_le_shadowArea tetrahedron B.unit_axis)
  have hsum : relativeCost tetrahedron C + relativeCost tetrahedron D +
      B₁.area / shadowArea tetrahedron B₁.axis +
      B₂.area / shadowArea tetrahedron B₂.axis ≤
      (familyArea C + familyArea D + B₁.area + B₂.area) /
        minimumShadowArea tetrahedron := by
    rw [add_div, add_div, add_div]
    linarith only [hC, hD, hB B₁, hB B₂]
  apply hsum.trans_lt
  apply (div_lt_iff₀ hmin).mpr
  linarith only [htotal]

theorem normalization : NormalizationStatement :=
  ⟨tetrahedron_eq_centered_translation, tetrahedron_minimumShadowArea,
    fun _ _ C D B₁ B₂ hcost => same_family_half_bounds C D B₁ B₂ hcost⟩

end CylinderCovering.SingularEdgeOneCover

end

end OAI
