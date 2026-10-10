import OAI.Geometry.CylinderCovering.Radial.EqualityCoverDefinitions
import OAI.Geometry.CylinderCovering.Rational.EqualityCover
import OAI.Geometry.CylinderCovering.Radial.TetraGeometry

namespace OAI

noncomputable section
namespace CylinderCovering.RadialEqualityCover
open Set TriangularCovering RadialPairedSweep

private abbrev identityIsometry : Space ≃ₗᵢ[ℝ] Space := LinearIsometryEquiv.refl ℝ Space

private lemma scale_height : 2 * SlopeRational.physicalScale = Real.sqrt 2 :=
  SlopeRational.twice_physicalScale

lemma tetrahedron_eq_dilation : tetrahedron (Real.sqrt 2) =
    Similarity.map (0 : Space) 4 identityIsometry '' SlopeRational.referenceTetrahedron := by
  ext z
  constructor
  · rintro ⟨x, y, t, hx, hy, rfl⟩
    refine ⟨RadialPairedSweep.point (x/4) (y/4) (Real.sqrt 2*t/4), ?_, ?_⟩
    · refine ⟨t/2, ?_, ?_, ?_, ?_, ?_⟩
      · linarith [abs_nonneg x]
      · linarith [abs_nonneg y]
      · change |x/4| ≤ (1/2+t/2)/2
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<4)]
        linarith
      · change |y/4| ≤ (1/2-t/2)/2
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<4)]
        linarith
      · change Real.sqrt 2*t/4 = SlopeRational.physicalScale*(t/2)
        rw [← scale_height]
        ring
    · ext i
      fin_cases i <;> simp [Similarity.map, identityIsometry, RadialPairedSweep.point] <;> ring
  · rintro ⟨z, ⟨t, ht0, ht1, hx, hy, hz⟩, rfl⟩
    refine ⟨4*z 0, 4*z 1, 2*t, ?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4)]
      linarith
    · rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4)]
      linarith
    · ext i
      fin_cases i
      · simp [Similarity.map, identityIsometry, RadialPairedSweep.point]
      · simp [Similarity.map, identityIsometry, RadialPairedSweep.point]
      · simp [Similarity.map, identityIsometry, RadialPairedSweep.point, hz, ← scale_height]
        ring

lemma firstBase_eq_dilation : firstBase =
    (fun z : Space => (4:ℝ) • z) '' SlopeRational.EqualityCover.firstBase := by
  ext z
  constructor
  · rintro ⟨y, t, ht0, ht1, hy, rfl⟩
    refine ⟨RuledApproximation.vec3 0 (y/4) (SlopeRational.physicalScale*(t/2)),
      ⟨!₂[y/4,t/2], ?_, rfl⟩, ?_⟩
    · change 0 ≤ t/2 ∧ t/2 ≤ 1/2 ∧ 2*|y/4| ≤ 1/2-t/2
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<4)]
      exact ⟨by linarith, by linarith, by linarith⟩
    · ext i
      fin_cases i <;> simp [RadialPairedSweep.point, RuledApproximation.vec3, ← scale_height] <;> ring
  · rintro ⟨z, ⟨p, ⟨hp0, hp1, hp2⟩, rfl⟩, rfl⟩
    refine ⟨4*p 0, 2*p 1, by linarith, by linarith, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4)]
      linarith
    · ext i
      fin_cases i <;> simp [RadialPairedSweep.point, RuledApproximation.vec3, ← scale_height]
      ring

lemma secondBase_eq_dilation : secondBase =
    (fun z : Space => (4:ℝ) • z) '' SlopeRational.EqualityCover.secondBase := by
  rw [secondBase, firstBase_eq_dilation, SlopeRational.EqualityCover.secondBase]
  simp only [Set.image_image]
  congr 1
  funext z
  ext i
  fin_cases i <;> simp [RadialPairedSweep.point, SlopeRational.reflection, RuledApproximation.vec3]

def cylinders (i : Fin 2) : TriCylinder :=
  (SlopeRational.EqualityCover.cylinders i).similarity 0 (r := 4) (by norm_num)
    identityIsometry

lemma cylinders_axis_zero : (cylinders 0).axis = firstAxis := by
  exact SlopeRational.EqualityCover.firstCylinder_axis

lemma cylinders_axis_one : (cylinders 1).axis = secondAxis := by
  exact SlopeRational.EqualityCover.secondCylinder_axis

lemma cylinders_base_zero : (cylinders 0).base = firstBase := by
  change Similarity.transportedBase SlopeRational.EqualityCover.firstCylinder.base
    SlopeRational.EqualityCover.firstCylinder.axis 0 4 identityIsometry = firstBase
  rw [SlopeRational.EqualityCover.firstCylinder_base, firstBase_eq_dilation]
  unfold Similarity.transportedBase
  apply congrArg (fun mapping : Space → Space => mapping '' SlopeRational.EqualityCover.firstBase)
  funext point
  simp [Similarity.baseMap, Similarity.project, identityIsometry]

lemma cylinders_base_one : (cylinders 1).base = secondBase := by
  change Similarity.transportedBase SlopeRational.EqualityCover.secondCylinder.base
    SlopeRational.EqualityCover.secondCylinder.axis 0 4 identityIsometry = secondBase
  rw [SlopeRational.EqualityCover.secondCylinder_base, secondBase_eq_dilation]
  unfold Similarity.transportedBase
  apply congrArg (fun mapping : Space → Space => mapping '' SlopeRational.EqualityCover.secondBase)
  funext point
  simp [Similarity.baseMap, Similarity.project, identityIsometry]

lemma cylinders_cover : triangularCovers (tetrahedron (Real.sqrt 2)) cylinders := by
  rw [tetrahedron_eq_dilation]
  rintro z ⟨w, hw, rfl⟩
  obtain ⟨i, hi⟩ := SlopeRational.EqualityCover.cylinders_covers w hw
  refine ⟨i, ?_⟩
  rw [cylinders, TriCylinder.similarity_carrier]
  exact ⟨w, hi, rfl⟩

lemma first_covers_nonnegative {z : Space}
    (hz : z ∈ tetrahedron (Real.sqrt 2)) (hlevel : 0 ≤ z 2) :
    z ∈ (cylinders 0).carrier := by
  rcases hz with ⟨x, y, t, hx, hy, rfl⟩
  have ht : 0 ≤ t := by
    change 0 ≤ Real.sqrt 2*t at hlevel
    exact nonneg_of_mul_nonneg_right hlevel (by positivity)
  refine ⟨RadialPairedSweep.point 0 y (Real.sqrt 2*t), ?_, x, ?_⟩
  · rw [cylinders_base_zero]
    exact ⟨y, t, ht, by linarith [abs_nonneg y], hy, rfl⟩
  · rw [cylinders_axis_zero]
    ext i
    fin_cases i <;> simp [firstAxis, RadialPairedSweep.point]

lemma secondBase_mem_iff (z : Space) : z ∈ secondBase ↔
    ∃ x t : ℝ, -1 ≤ t ∧ t ≤ 0 ∧ |x| ≤ 1+t ∧
      z = RadialPairedSweep.point x 0 (Real.sqrt 2*t) := by
  constructor
  · rintro ⟨w, ⟨y, t, ht0, ht1, hy, rfl⟩, rfl⟩
    refine ⟨y, -t, by linarith, by linarith, by linarith, ?_⟩
    ext i
    fin_cases i <;> simp [RadialPairedSweep.point]
  · rintro ⟨x, t, ht0, ht1, hx, rfl⟩
    refine ⟨RadialPairedSweep.point 0 x (Real.sqrt 2*(-t)),
      ⟨x, -t, by linarith, by linarith, by simpa using hx, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [RadialPairedSweep.point]

lemma second_covers_nonpositive {z : Space}
    (hz : z ∈ tetrahedron (Real.sqrt 2)) (hlevel : z 2 ≤ 0) :
    z ∈ (cylinders 1).carrier := by
  rcases hz with ⟨x, y, t, hx, hy, rfl⟩
  have ht : t ≤ 0 := by
    change Real.sqrt 2*t ≤ 0 at hlevel
    exact nonpos_of_mul_nonpos_right hlevel (by positivity)
  refine ⟨RadialPairedSweep.point x 0 (Real.sqrt 2*t), ?_, y, ?_⟩
  · rw [cylinders_base_one, secondBase_mem_iff]
    exact ⟨x, t, by linarith [abs_nonneg x], ht, hx, rfl⟩
  · rw [cylinders_axis_one]
    ext i
    fin_cases i <;> simp [secondAxis, RadialPairedSweep.point]

lemma cylinders_area_each (i : Fin 2) : area (cylinders i).base = Real.sqrt 2 := by
  rw [cylinders, TriCylinder.similarity_area,
    SlopeRational.EqualityCover.cylinders_area_each, ← scale_height]
  ring

lemma cylinders_totalArea : totalArea cylinders = 2 * Real.sqrt 2 := by
  simp [totalArea, cylinders_area_each]

lemma cylinders_shadow_each (i : Fin 2) :
    shadowArea (tetrahedron (Real.sqrt 2)) (cylinders i).axis = 4 * Real.sqrt 2 := by
  rw [tetrahedron_eq_dilation]
  change Similarity.shadowArea
    (Similarity.map (0:Space) 4 identityIsometry '' SlopeRational.referenceTetrahedron)
    (identityIsometry (SlopeRational.EqualityCover.cylinders i).axis) = _
  rw [Similarity.shadowArea_map]
  · change 4^2 * shadowArea SlopeRational.referenceTetrahedron
      (SlopeRational.EqualityCover.cylinders i).axis = _
    rw [SlopeRational.EqualityCover.cylinders_shadow_each, ← scale_height]
    ring
  · norm_num

lemma cylinders_relativeCost :
    triangularRelativeCost (tetrahedron (Real.sqrt 2)) cylinders = 1/2 := by
  simp only [triangularRelativeCost, cylinders_area_each, cylinders_shadow_each,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem equality_cover : Statement := by
  refine ⟨cylinders, cylinders_axis_zero, cylinders_axis_one,
    cylinders_base_zero, cylinders_base_one, cylinders_cover,
    cylinders_area_each, cylinders_totalArea, ?_, cylinders_shadow_each,
    cylinders_relativeCost⟩
  rw [cylinders_totalArea, reference_minimum]
  ring

end CylinderCovering.RadialEqualityCover

end

end OAI
