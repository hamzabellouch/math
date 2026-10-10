import OAI.Geometry.CylinderCovering.Singular.EdgeOneGeometryDefinitions
import OAI.Geometry.CylinderCovering.Singular.EdgeOne
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SingularEdgeOne
open RuledApproximation

lemma fieldP_eq_ruled (p b r : ℝ) :
    fieldP p b r = singularField p (vec2 b r) 0 := by
  unfold fieldP singularField
  simp only [vec2_apply_zero, vec2_apply_one]
  rw [show r / (1 / 2 : ℝ) = 2 * r by ring]
  ring

lemma fieldQ_eq_ruled (p b r : ℝ) :
    fieldQ p b r = singularField p (vec2 b r) 1 := by
  unfold fieldQ singularField
  simp only [vec2_apply_zero, vec2_apply_one]
  rw [show r / (1 / 2 : ℝ) = 2 * r by ring]

lemma ceiling_eq_ruled (p b : ℝ) : ceiling p b = ceilingPolynomial p b := by
  unfold ceiling ceilingPolynomial
  ring

lemma coefficient_eq_ruled (p : ℝ) : coefficient p = singularCoefficient p := rfl

lemma edgeDomain0_isCompact : IsCompact edgeDomain0 := by
  apply (coneTriangle_isCompact (1 / 2)).of_isClosed_subset
  · unfold edgeDomain0
    exact (isClosed_le (f := fun _ : Plane => (0 : ℝ)) (g := fun z => z 1)
      (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (f := fun z : Plane => z 1) (g := fun _ => (1 / 2 : ℝ))
        (by fun_prop) (by fun_prop)).inter
        (isClosed_le (f := fun z : Plane => |z 0|) (g := fun z => z 1 / 2)
          (by fun_prop) (by fun_prop)))
  · intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans (by linarith [hz.1])⟩

lemma edgeEnergy_eq_ruled (p : ℝ) {w l : ℝ} (hl : 0 < l) :
    edgeEnergy p w l = singularEnergy p (vec2 (2 * w) l) / 32 := by
  unfold edgeEnergy singularEnergy
  rw [edgeU_eq, edgeV_eq p w hl, fieldP_eq_ruled, fieldQ_eq_ruled]
  ring

lemma edgeEnergy_nonneg (p w l : ℝ) : 0 ≤ edgeEnergy p w l := by
  unfold edgeEnergy
  positivity

lemma edgeEnergy_measurable (p : ℝ) :
    Measurable (fun z : Plane => edgeEnergy p (z 0) (z 1)) := by
  unfold edgeEnergy edgeU edgeV
  fun_prop

lemma edgeEnergy_on_domain_eq {p : ℝ} (hp : 1 < p) {z : Plane} (hz : z ∈ edgeDomain0) :
    edgeEnergy p (z 0) (z 1) = singularEnergy p (vec2 (2 * z 0) (z 1)) / 32 := by
  by_cases hl : z 1 = 0
  · have hw : z 0 = 0 := abs_nonpos_iff.mp (by simpa only [hl, zero_div] using hz.2.2)
    simp [hl, hw, edgeEnergy, edgeU, edgeV, singularEnergy, singularField, vec2,
      Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
  · exact edgeEnergy_eq_ruled p (lt_of_le_of_ne hz.1 (Ne.symm hl))

lemma edgeEnergy_integrable {p : ℝ} (hp : 1 < p) :
    IntegrableOn (fun z : Plane => edgeEnergy p (z 0) (z 1)) edgeDomain0 := by
  obtain ⟨C, hC, hbound⟩ := singularEnergy_bounded hp
  apply IntegrableOn.of_bound edgeDomain0_isCompact.measure_lt_top
    (edgeEnergy_measurable p).aestronglyMeasurable (C / 32)
  filter_upwards [ae_restrict_mem edgeDomain0_isCompact.measurableSet] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (edgeEnergy_nonneg p _ _), edgeEnergy_on_domain_eq hp hz]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply hbound
  change 0 ≤ z 1 ∧ z 1 ≤ 2 ∧ |2 * z 0| ≤ z 1
  refine ⟨hz.1, hz.2.1.trans (by norm_num), ?_⟩
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [hz.2.2]

lemma edgeG_integral {p : ℝ} (hp : 1 < p) :
    (∫ z in edgeDomain0, edgeEnergy p (z 0) (z 1)) = edgeG p := by
  have heq : ∀ z : Plane, z ∈ edgeDomain0 ↔
      z 1 ∈ Icc (0 : ℝ) (1 / 2) ∧ z 0 ∈ Icc (-z 1 / 2) (z 1 / 2) := by
    intro z
    simp only [edgeDomain0, mem_ofPred_eq, mem_Icc, abs_le]
    constructor
    · rintro ⟨h0, h1, h2, h3⟩
      exact ⟨⟨h0, h1⟩, ⟨by linarith, h3⟩⟩
    · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
      exact ⟨h0, h1, ⟨by linarith, h3⟩⟩
  rw [plane_setIntegral_horizontal_interval edgeDomain0_isCompact.measurableSet
    (edgeEnergy_integrable hp) (s := Icc (0 : ℝ) (1 / 2))
    (l := fun l => -l / 2) (u := fun l => l / 2) measurableSet_Icc heq]
  have he : (∫ l in Icc (0 : ℝ) (1 / 2),
      ∫ w in Icc (-l / 2) (l / 2), edgeEnergy p w l) =
      (∫ l in (0 : ℝ)..(1 / 2 : ℝ),
        ∫ w in (-l / 2)..(l / 2), edgeEnergy p w l) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro l hl
    dsimp only
    rw [intervalIntegral.integral_of_le (by linarith [hl.1] : -l / 2 ≤ l / 2),
      ← integral_Icc_eq_integral_Ioc]
  simpa only [vec2_apply_zero, vec2_apply_one] using he.trans (edgeG_iterated_integral (by linarith))

lemma height_factor : Real.sqrt 2 / 2 = (1 / Real.sqrt 2 : ℝ) := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma physicalSimilarity_vec3 (x y z : ℝ) :
    physicalSimilarity (vec3 x y z) = vec3 (y / 2) (x / 2) (z / 2) := rfl

lemma physicalSimilarity_tetrahedron : physicalSimilarity '' tetrahedron = edgeTetrahedron := by
  ext z
  constructor
  · rintro ⟨x, ⟨t, ht0, ht1, hx, hy, hz⟩, rfl⟩
    refine ⟨t, ht0, ht1, ?_, ?_, ?_⟩
    · change |x 1 / 2| ≤ t / 2
      exact (cone_dictionary (x 1) t).2 hy
    · change |x 0 / 2| ≤ (1 - t) / 2
      exact (cone_dictionary (x 0) (1 - t)).2 hx
    · change x 2 / 2 = (1 / Real.sqrt 2) * t
      rw [hz, show Real.sqrt 2 * t / 2 = (Real.sqrt 2 / 2) * t by ring, height_factor]
  · rintro ⟨t, ht0, ht1, hx, hy, hz⟩
    refine ⟨vec3 (2 * z 1) (2 * z 0) (2 * z 2), ?_, ?_⟩
    · refine ⟨t, ht0, ht1, ?_, ?_, ?_⟩
      · change |2 * z 1| ≤ 1 - t
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      · change |2 * z 0| ≤ t
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      · change 2 * z 2 = Real.sqrt 2 * t
        rw [hz, ← height_factor]
        ring
    · ext i
      fin_cases i <;> simp [physicalSimilarity, vec3]

lemma edgeU_labelMap (p : ℝ) (z : Plane) :
    edgeU p (labelMap z 0) (labelMap z 1) = singularField p z 0 / 4 := by
  change edgeU p (z 0 / 2) (z 1) = _
  rw [edgeU_eq, show 2 * (z 0 / 2) = z 0 by ring, fieldP_eq_ruled, vec2_coordinates]

lemma edgeV_labelMap (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    edgeV p (labelMap z 0) (labelMap z 1) = singularField p z 1 / 2 := by
  change edgeV p (z 0 / 2) (z 1) = _
  rw [edgeV_eq p (z 0 / 2) hz, show 2 * (z 0 / 2) = z 0 by ring,
    fieldQ_eq_ruled, vec2_coordinates]

lemma physicalSimilarity_lower (p c : ℝ) {D : Set Plane}
    (hD : ∀ b ∈ D, 0 < b 1) :
    physicalSimilarity '' physicalRuled (Real.sqrt 2) D
      (fun b => c • singularField p b) 1 = edgeLower p (4 * c) (labelMap '' D) := by
  ext z
  constructor
  · rintro ⟨q, ⟨b, hb, s, hs, rfl⟩, rfl⟩
    refine ⟨labelMap b, ⟨b, hb, rfl⟩, s / 2, ?_, ?_⟩
    · exact (cone_dictionary s 1).2 hs
    · ext i
      fin_cases i
      · change (b 0 + s * (c * singularField p b 0)) / 2 =
          b 0 / 2 + (4 * c) * (s / 2) * edgeU p (labelMap b 0) (labelMap b 1)
        rw [edgeU_labelMap]
        ring
      · change s / 2 = s / 2
        rfl
      · change Real.sqrt 2 * (b 1 + s * (c * singularField p b 1)) / 2 =
          (1 / Real.sqrt 2) *
            (b 1 + (4 * c) * (s / 2) * edgeV p (labelMap b 0) (labelMap b 1))
        rw [edgeV_labelMap p (hD b hb), ← height_factor]
        ring
  · rintro ⟨b', ⟨b, hb, rfl⟩, y, hy, rfl⟩
    let q := vec3 (2 * y) (b 0 + (2 * y) * (c * singularField p b 0))
      (Real.sqrt 2 * (b 1 + (2 * y) * (c * singularField p b 1)))
    refine ⟨q, ⟨b, hb, 2 * y, ?_, rfl⟩, ?_⟩
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · ext i
      fin_cases i
      · change (b 0 + (2 * y) * (c * singularField p b 0)) / 2 =
          b 0 / 2 + (4 * c) * y * edgeU p (labelMap b 0) (labelMap b 1)
        rw [edgeU_labelMap]
        ring
      · change (2 * y) / 2 = y
        ring
      · change Real.sqrt 2 * (b 1 + (2 * y) * (c * singularField p b 1)) / 2 =
          (1 / Real.sqrt 2) *
            (b 1 + (4 * c) * y * edgeV p (labelMap b 0) (labelMap b 1))
        rw [edgeV_labelMap p (hD b hb), ← height_factor]
        ring

lemma physicalSimilarity_upper (p c : ℝ) {D : Set Plane}
    (hD : ∀ b ∈ D, 0 < b 1) :
    physicalSimilarity '' upperSegments p c D = edgeUpper p (4 * c) (labelMap '' D) := by
  ext z
  constructor
  · rintro ⟨q, ⟨b, hb, s, hs, rfl⟩, rfl⟩
    refine ⟨labelMap b, ⟨b, hb, rfl⟩, s / 2, (cone_dictionary s 1).2 hs, ?_⟩
    ext i
    fin_cases i
    · change s / 2 = s / 2
      rfl
    · change (b 0 - c * s * singularField p b 0) / 2 =
        b 0 / 2 - (4 * c) * (s / 2) * edgeU p (labelMap b 0) (labelMap b 1)
      rw [edgeU_labelMap]
      ring
    · change Real.sqrt 2 * (1 - (b 1 - c * s * singularField p b 1)) / 2 =
        (1 / Real.sqrt 2) *
          (1 - (b 1 - (4 * c) * (s / 2) * edgeV p (labelMap b 0) (labelMap b 1)))
      rw [edgeV_labelMap p (hD b hb), ← height_factor]
      ring
  · rintro ⟨b', ⟨b, hb, rfl⟩, x, hx, rfl⟩
    let q := vec3 (b 0 - c * (2 * x) * singularField p b 0) (2 * x)
      (Real.sqrt 2 * (1 - (b 1 - c * (2 * x) * singularField p b 1)))
    refine ⟨q, ⟨b, hb, 2 * x, ?_, rfl⟩, ?_⟩
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · ext i
      fin_cases i
      · change (2 * x) / 2 = x
        ring
      · change (b 0 - c * (2 * x) * singularField p b 0) / 2 =
          b 0 / 2 - (4 * c) * x * edgeU p (labelMap b 0) (labelMap b 1)
        rw [edgeU_labelMap]
        ring
      · change Real.sqrt 2 * (1 - (b 1 - c * (2 * x) * singularField p b 1)) / 2 =
          (1 / Real.sqrt 2) *
            (1 - (b 1 - (4 * c) * x * edgeV p (labelMap b 0) (labelMap b 1)))
        rw [edgeV_labelMap p (hD b hb), ← height_factor]
        ring

lemma upperSegments_canonical (p gamma c : ℝ) :
    upperSegments p c (singularDomain p gamma c) = singularUpper p gamma c := rfl

end SingularEdgeOne

end

end OAI
