import OAI.Geometry.CylinderCovering.Physical.MinimumDefinitions
import OAI.Geometry.CylinderCovering.Radial.TetraGeometry
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity

namespace OAI

open Set
open scoped InnerProductSpace
noncomputable section
namespace RadialPhysical.PhysicalMinimum
open CylinderCovering

private abbrev canonicalBody := RadialPairedSweep.tetrahedron (Real.sqrt 2)

lemma centered_similarity {b : ℝ} (hb : 0 < b) :
    modelBody true b = Similarity.map (0 : Space) b
      (LinearIsometryEquiv.refl ℝ Space) '' canonicalBody := by
  ext z
  constructor
  · rintro ⟨x, y, t, hx, hy, rfl⟩
    refine ⟨RadialPairedSweep.point (x/b) (y/b) (Real.sqrt 2*t), ?_, ?_⟩
    · refine ⟨x/b, y/b, t, ?_, ?_, rfl⟩
      · rw [abs_div, abs_of_pos hb]
        exact (div_le_iff₀ hb).2 (by nlinarith only [hx])
      · rw [abs_div, abs_of_pos hb]
        exact (div_le_iff₀ hb).2 (by nlinarith only [hy])
    · ext i
      fin_cases i <;> simp [Similarity.map, RadialPairedSweep.point, point, height] <;>
        field_simp
  · rintro ⟨_, ⟨x, y, t, hx, hy, rfl⟩, rfl⟩
    refine ⟨b*x, b*y, t, ?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos hb]
      exact mul_le_mul_of_nonneg_left hx hb.le
    · rw [abs_mul, abs_of_pos hb]
      exact mul_le_mul_of_nonneg_left hy hb.le
    · ext i
      fin_cases i <;> simp [Similarity.map, RadialPairedSweep.point, point, height]
      ring

lemma halfheight_similarity {b : ℝ} (hb : 0 < b) :
    modelBody false b = Similarity.map (point b 0 0 (1/2)) (b/2)
      (LinearIsometryEquiv.refl ℝ Space) '' canonicalBody := by
  ext z
  constructor
  · rintro ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩
    refine ⟨RadialPairedSweep.point (2*x/b) (2*y/b) (Real.sqrt 2*(2*t-1)), ?_, ?_⟩
    · refine ⟨2*x/b, 2*y/b, 2*t-1, ?_, ?_, rfl⟩
      · rw [abs_div, abs_of_pos hb, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
        exact (div_le_iff₀ hb).2 (by nlinarith only [hx])
      · rw [abs_div, abs_of_pos hb, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
        exact (div_le_iff₀ hb).2 (by nlinarith only [hy])
    · ext i
      fin_cases i <;> simp [Similarity.map, RadialPairedSweep.point, point, height,
        ne_of_gt hb]
      field_simp
      ring
  · rintro ⟨_, ⟨x, y, t, hx, hy, rfl⟩, rfl⟩
    have ht0 : -1 ≤ t := by linarith [abs_nonneg x]
    have ht1 : t ≤ 1 := by linarith [abs_nonneg y]
    refine ⟨b/2*x, b/2*y, (t+1)/2, by linarith, by linarith, ?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos (by positivity : 0 < b/2)]
      nlinarith only [mul_le_mul_of_nonneg_left hx (show 0 ≤ b/2 by positivity)]
    · rw [abs_mul, abs_of_pos (by positivity : 0 < b/2)]
      nlinarith only [mul_le_mul_of_nonneg_left hy (show 0 ≤ b/2 by positivity)]
    · ext i
      fin_cases i <;> simp [Similarity.map, RadialPairedSweep.point, point, height]
      ring

theorem minimum_modelBody (centered : Bool) {b : ℝ} (hb : 0 < b) :
    Similarity.minimumArea (modelBody centered b) =
      (if centered then 4 else 1) * b * height b := by
  have hmin : Similarity.minimumArea canonicalBody = 4 * Real.sqrt 2 :=
    RadialPairedSweep.reference_minimum
  cases centered
  · rw [halfheight_similarity hb, Similarity.minimumArea_map _ _
      (by positivity : b/2 ≠ 0) (LinearIsometryEquiv.refl ℝ Space), hmin]
    simp only [Bool.false_eq_true, ite_false, one_mul, height]
    ring
  · rw [centered_similarity hb, Similarity.minimumArea_map _ _
      (ne_of_gt hb) (LinearIsometryEquiv.refl ℝ Space), hmin]
    simp only [ite_true, height]
    ring

theorem shadow_x_modelBody (centered : Bool) {b : ℝ} (hb : 0 < b) :
    Similarity.shadowArea (modelBody centered b) (TriangularCovering.tiltV 0 0 0) =
      (if centered then 4 else 1)*b*height b := by
  have hx : Similarity.shadowArea canonicalBody (TriangularCovering.tiltV 0 0 0) =
      4 * Real.sqrt 2 := by
    change CylinderCovering.shadowArea canonicalBody (TriangularCovering.tiltV 0 0 0) = _
    rw [RadialPairedSweep.shadowArea_eq_cubic, Cubic.K4_shadow,
      TriangularCovering.xAxis_shadow]
    rfl
  cases centered
  · rw [halfheight_similarity hb]
    rw [show Similarity.shadowArea
        (Similarity.map (point b 0 0 (1/2)) (b/2)
          (LinearIsometryEquiv.refl ℝ Space) '' canonicalBody)
        (TriangularCovering.tiltV 0 0 0) =
        (b/2)^2 * Similarity.shadowArea canonicalBody (TriangularCovering.tiltV 0 0 0) from
      Similarity.shadowArea_map _ _ (by positivity : b/2 ≠ 0) _ _]
    rw [hx]
    simp only [Bool.false_eq_true, ite_false, height]
    ring
  · rw [centered_similarity hb]
    rw [show Similarity.shadowArea
        (Similarity.map 0 b (LinearIsometryEquiv.refl ℝ Space) '' canonicalBody)
        (TriangularCovering.tiltV 0 0 0) =
        b^2 * Similarity.shadowArea canonicalBody (TriangularCovering.tiltV 0 0 0) from
      Similarity.shadowArea_map _ _ (ne_of_gt hb) _ _]
    rw [hx]
    simp only [ite_true, height]
    ring

theorem minimum_attained (centered : Bool) {b : ℝ} (hb : 0 < b) :
    ∃ u : Space, ‖u‖ = 1 ∧
      Similarity.shadowArea (modelBody centered b) u =
        Similarity.minimumArea (modelBody centered b) := by
  refine ⟨TriangularCovering.tiltV 0 0 0, TriangularCovering.xAxis_unit, ?_⟩
  rw [shadow_x_modelBody centered hb, minimum_modelBody centered hb]

theorem nonorthonormal_minimum :
    Similarity.minimumArea {z : Space | ∃ p q t : ℝ,
      |p| ≤ 1+t ∧ |q| ≤ 1-t ∧ z = nonorthPoint p q t} = 2*Real.sqrt 2 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hpoint (p q t : ℝ) :
      Similarity.map 0 (1/Real.sqrt 2) (LinearIsometryEquiv.refl ℝ Space)
        (RadialPairedSweep.point p q (Real.sqrt 2*t)) = nonorthPoint p q t := by
    ext i
    fin_cases i <;> simp [Similarity.map, RadialPairedSweep.point, nonorthPoint, hs] <;>
      field_simp
  have hset : {z : Space | ∃ p q t : ℝ,
      |p| ≤ 1+t ∧ |q| ≤ 1-t ∧ z = nonorthPoint p q t} =
      Similarity.map 0 (1/Real.sqrt 2) (LinearIsometryEquiv.refl ℝ Space) '' canonicalBody := by
    ext z
    constructor
    · rintro ⟨p,q,t,hp,hq,rfl⟩
      exact ⟨RadialPairedSweep.point p q (Real.sqrt 2*t), ⟨p,q,t,hp,hq,rfl⟩,
        hpoint p q t⟩
    · rintro ⟨_,⟨p,q,t,hp,hq,rfl⟩,rfl⟩
      exact ⟨p,q,t,hp,hq,hpoint p q t⟩
  rw [hset, Similarity.minimumArea_map _ _ (one_div_ne_zero hs)
    (LinearIsometryEquiv.refl ℝ Space)]
  have hmin : Similarity.minimumArea canonicalBody = 4*Real.sqrt 2 :=
    RadialPairedSweep.reference_minimum
  rw [hmin, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

theorem halfheight_reference {b : ℝ} (hb : 0 < b) :
    Similarity.minimumArea (tetrahedron b) / 2 = b * height b / 2 := by
  have h := minimum_modelBody false hb
  simpa [modelBody] using congrArg (fun x : ℝ => x/2) h

theorem centered_reference {b : ℝ} (hb : 0 < b) :
    Similarity.minimumArea (modelBody true b) / 2 = 2 * b * height b := by
  rw [minimum_modelBody true hb]
  simp only [ite_true]
  ring

lemma reference_pos (centered : Bool) {b : ℝ} (hb : 0 < b) :
    0 < (if centered then (4:ℝ) else 1) * b * height b := by
  cases centered <;> simp only [Bool.false_eq_true, ite_false, ite_true, height] <;> positivity

theorem shadow_lower (centered : Bool) {b : ℝ} (hb : 0 < b)
    (u : Space) (hu : ‖u‖ = 1) :
    (if centered then 4 else 1) * b * height b ≤
      CylinderCovering.shadowArea (modelBody centered b) u := by
  rw [← minimum_modelBody centered hb]
  exact Similarity.minimumArea_le_shadowArea _ hu

theorem relativeCost_le {n : ℕ} (centered : Bool) {b : ℝ} (hb : 0 < b)
    (C : Fin n → TriangularCovering.TriCylinder) :
    triangularRelativeCost (modelBody centered b) C ≤
      TriangularCovering.totalArea C / ((if centered then 4 else 1)*b*height b) := by
  unfold triangularRelativeCost TriangularCovering.totalArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg (reference_pos centered hb)
    (shadow_lower centered hb (C i).axis (C i).unit_axis)

theorem both_half_bounds {n : ℕ} (centered : Bool) {b : ℝ} (hb : 0 < b)
    (C : Fin n → TriangularCovering.TriCylinder)
    (hcost : TriangularCovering.totalArea C <
      ((if centered then 4 else 1)*b*height b)/2) :
    TriangularCovering.totalArea C < minimumShadowArea (modelBody centered b)/2 ∧
    triangularRelativeCost (modelBody centered b) C < 1/2 := by
  refine ⟨?_, (relativeCost_le centered hb C).trans_lt ?_⟩
  · change TriangularCovering.totalArea C < Similarity.minimumArea (modelBody centered b)/2
    rwa [minimum_modelBody centered hb]
  · exact (div_lt_iff₀ (reference_pos centered hb)).2 (by linarith)

theorem baseRelativeCost_le {ι : Type*} [Fintype ι]
    (centered : Bool) {b : ℝ} (hb : 0 < b)
    (B : ι → Set Space) (u : ι → Space) (hu : ∀ i, ‖u i‖ = 1) :
    (∑ i, TriangularCovering.area (B i) /
      CylinderCovering.shadowArea (modelBody centered b) (u i)) ≤
    (∑ i, TriangularCovering.area (B i)) /
      ((if centered then 4 else 1)*b*height b) := by
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun i _ =>
    div_le_div_of_nonneg_left ENNReal.toReal_nonneg (reference_pos centered hb)
      (shadow_lower centered hb (u i) (hu i))

lemma upperAxis_unit (b eta s : ℝ) : ‖upperPhysicalAxis b eta s‖ = 1 := by
  have hv : point b 1 (-eta*(s^2+b^2)/2) (eta*s) ≠ 0 := by
    intro h
    have h0 := congrArg (fun z : Space => z 0) h
    norm_num [point] at h0
  unfold upperPhysicalAxis
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma lowerAxis_unit (b eta s : ℝ) : ‖lowerPhysicalAxis b eta s‖ = 1 := by
  have hv : point b (eta*(s^2+b^2)/2) 1 (eta*s) ≠ 0 := by
    intro h
    have h1 := congrArg (fun z : Space => z 1) h
    norm_num [point] at h1
  unfold lowerPhysicalAxis
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem actual_relativeCost_le (centered : Bool) {b : ℝ} (hb : 0 < b)
    (eta : ℝ) (T : ℝ → ℝ) (N : ℕ) (tagU tagL : Fin N → ℝ) :
    (∑ i, TriangularCovering.area (upperPhysicalBase centered b eta T N tagU i) /
      CylinderCovering.shadowArea (modelBody centered b) (upperPhysicalAxis b eta (tagU i))) +
    (∑ i, TriangularCovering.area (lowerPhysicalBase centered b eta T N tagL i) /
      CylinderCovering.shadowArea (modelBody centered b) (lowerPhysicalAxis b eta (tagL i))) ≤
      physicalActualCost centered b eta T N tagU tagL /
        ((if centered then 4 else 1)*b*height b) := by
  unfold physicalActualCost
  rw [add_div]
  exact add_le_add
    (baseRelativeCost_le centered hb _ _ (fun i => upperAxis_unit b eta (tagU i)))
    (baseRelativeCost_le centered hb _ _ (fun i => lowerAxis_unit b eta (tagL i)))

theorem actual_half_bound (centered : Bool) {b : ℝ} (hb : 0 < b)
    (eta : ℝ) (T : ℝ → ℝ) (N : ℕ) (tagU tagL : Fin N → ℝ)
    (hcost : physicalActualCost centered b eta T N tagU tagL <
      ((if centered then 4 else 1)*b*height b)/2) :
    (∑ i, TriangularCovering.area (upperPhysicalBase centered b eta T N tagU i) /
      CylinderCovering.shadowArea (modelBody centered b) (upperPhysicalAxis b eta (tagU i))) +
    (∑ i, TriangularCovering.area (lowerPhysicalBase centered b eta T N tagL i) /
      CylinderCovering.shadowArea (modelBody centered b) (lowerPhysicalAxis b eta (tagL i))) < 1/2 := by
  apply (actual_relativeCost_le centered hb eta T N tagU tagL).trans_lt
  exact (div_lt_iff₀ (reference_pos centered hb)).2 (by linarith)

theorem physical_minimum : Statement := by
  refine ⟨?_, nonorthonormal_minimum, ?_⟩
  · intro centered b hb
    exact ⟨minimum_modelBody centered hb, minimum_attained centered hb,
      shadow_lower centered hb, fun _ C hC => both_half_bounds centered hb C hC⟩
  · intro centered b hb eta T N tagU tagL hcost
    refine ⟨?_, actual_half_bound centered hb eta T N tagU tagL hcost⟩
    change physicalActualCost centered b eta T N tagU tagL <
      Similarity.minimumArea (modelBody centered b)/2
    rwa [minimum_modelBody centered hb]

end RadialPhysical.PhysicalMinimum

end

end OAI
