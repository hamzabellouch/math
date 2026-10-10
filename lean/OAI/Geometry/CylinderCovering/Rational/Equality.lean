import OAI.Geometry.CylinderCovering.Rational.EqualityDefinitions
import OAI.Geometry.CylinderCovering.Rational.CostActual
import OAI.Geometry.CylinderCovering.Rational.Realization
import OAI.Geometry.CylinderCovering.Rational.EnergyIntegral

namespace OAI

open Set MeasureTheory
noncomputable section
namespace SlopeRational

lemma baseDomain_triangle : RuledApproximation.IsTriangle baseDomain := by
  refine ⟨vec2 (-1 / 4) 0, vec2 (1 / 2) 0, vec2 (1 / 4) (1 / 2), ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t he
    have h0 := congrArg (fun z : Plane => z 0) he
    have h1 := congrArg (fun z : Plane => z 1) he
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vec2_zero, vec2_one,
      PiLp.zero_apply] at h0 h1
    constructor <;> linarith
  · ext z
    constructor
    · rintro ⟨hw, ht⟩
      change 2 * |z 0| ≤ 1 / 2 - z 1 at hw
      change 0 ≤ z 1 at ht
      have hab := abs_le.mp (show |z 0| ≤ (1 / 2 - z 1) / 2 by linarith)
      refine ⟨2 * z 0 + 1 / 2 - z 1, 2 * z 1,
        by linarith [hab.1], by linarith, by linarith [hab.2], ?_⟩
      ext i
      fin_cases i <;> simp [vec2] <;> ring
    · rintro ⟨s, t, hs, ht, hst, rfl⟩
      change 2 * |(-1 / 4 : ℝ) + s * (1 / 2) + t * (1 / 4)| ≤
        1 / 2 - (0 + s * 0 + t * (1 / 2)) ∧ 0 ≤ 0 + s * 0 + t * (1 / 2)
      constructor
      · have h : |(-1 / 4 : ℝ) + s * (1 / 2) + t * (1 / 4)| ≤
            (1 / 2 - (0 + s * 0 + t * (1 / 2))) / 2 := by
          apply abs_le.mpr
          constructor <;> linarith
        linarith
      · positivity

def equalityLowerCylinder : RuledApproximation.Cylinder :=
  RuledApproximation.projectedCylinder physicalScale 0 baseDomain

def equalityUpperCylinder : RuledApproximation.Cylinder :=
  equalityLowerCylinder.rotate reflectionIsometry

lemma equalityLowerCylinder_axis :
    equalityLowerCylinder.axis = RuledApproximation.vec3 1 0 0 := by
  have hn : ‖RuledApproximation.physicalDirection physicalScale 0‖ = 1 := by
    have hs := RuledApproximation.physicalDirection_norm_sq physicalScale 0
    simp only [PiLp.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, add_zero] at hs
    nlinarith [norm_nonneg (RuledApproximation.physicalDirection physicalScale 0)]
  change ‖RuledApproximation.physicalDirection physicalScale 0‖⁻¹ •
    RuledApproximation.physicalDirection physicalScale 0 = _
  rw [hn]
  simp [RuledApproximation.physicalDirection]

lemma equalityUpperCylinder_axis :
    equalityUpperCylinder.axis = RuledApproximation.vec3 0 1 0 := by
  change reflectionIsometry equalityLowerCylinder.axis = _
  rw [equalityLowerCylinder_axis]
  ext i
  fin_cases i <;> simp [reflectionIsometry, reflection, RuledApproximation.vec3]

lemma equalityLowerCylinder_triangle : equalityLowerCylinder.triangle :=
  baseDomain_triangle.linear_image _
    (RuledApproximation.perpendicularProjection_injective physicalScale_pos 0)

lemma equalityUpperCylinder_triangle : equalityUpperCylinder.triangle :=
  RuledApproximation.Cylinder.rotate_triangle equalityLowerCylinder_triangle reflectionIsometry

lemma equalityLowerCylinder_area : equalityLowerCylinder.area = physicalScale / 8 := by
  rw [equalityLowerCylinder, RuledApproximation.projectedCylinder_area physicalScale_pos,
    RationalEnergy.baseDomain_volume]
  simp [RuledApproximation.physicalWeight]
  ring

lemma equalityUpperCylinder_area : equalityUpperCylinder.area = physicalScale / 8 := by
  rw [equalityUpperCylinder, RuledApproximation.Cylinder.rotate_area, equalityLowerCylinder_area]

theorem equality_cylinders_cover :
    referenceTetrahedron ⊆ equalityLowerCylinder.carrier ∪ equalityUpperCylinder.carrier := by
  intro z hz
  obtain ⟨t, htlo, hthi, hx, hy, hz2⟩ := hz
  by_cases ht : 0 ≤ t
  · left
    rw [equalityLowerCylinder, RuledApproximation.projectedCylinder_mem_iff]
    refine ⟨vec2 (z 1) t, ⟨?_, ht⟩, z 0, ?_⟩
    · change 2 * |z 1| ≤ 1 / 2 - t
      linarith
    · ext i
      fin_cases i <;>
        simp [RuledApproximation.planeEmbedding, RuledApproximation.physicalDirection,
          RuledApproximation.vec3, vec2, hz2]
  · right
    rw [equalityUpperCylinder, RuledApproximation.Cylinder.rotate_carrier]
    refine ⟨reflection z, ?_, ?_⟩
    · rw [equalityLowerCylinder, RuledApproximation.projectedCylinder_mem_iff]
      refine ⟨vec2 (z 0) (-t), ⟨?_, by change 0 ≤ -t; linarith⟩, z 1, ?_⟩
      · change 2 * |z 0| ≤ 1 / 2 - -t
        linarith
      · ext i
        fin_cases i <;>
          simp [reflection, RuledApproximation.planeEmbedding,
            RuledApproximation.physicalDirection, RuledApproximation.vec3, vec2, hz2]
    · ext i
      fin_cases i <;> simp [reflectionIsometry, reflection, RuledApproximation.vec3]

theorem two_cylinder_equality_configuration :
    ∃ C D : RuledApproximation.Cylinder,
      C.triangle ∧ D.triangle ∧
      referenceTetrahedron ⊆ C.carrier ∪ D.carrier ∧
      C.area = physicalScale / 8 ∧ D.area = physicalScale / 8 ∧
      C.area + D.area = physicalScale / 4 := by
  refine ⟨equalityLowerCylinder, equalityUpperCylinder, equalityLowerCylinder_triangle,
    equalityUpperCylinder_triangle, equality_cylinders_cover,
    equalityLowerCylinder_area, equalityUpperCylinder_area, ?_⟩
  rw [equalityLowerCylinder_area, equalityUpperCylinder_area]
  ring

theorem equalityConfiguration_main : EqualityConfigurationStatement := by
  refine ⟨equalityLowerCylinder, equalityUpperCylinder,
    equalityLowerCylinder_axis, equalityUpperCylinder_axis,
    equalityLowerCylinder_triangle, equalityUpperCylinder_triangle,
    equalityLowerCylinder_triangle.isCompact, equalityUpperCylinder_triangle.isCompact,
    equality_cylinders_cover, equalityLowerCylinder_area, equalityUpperCylinder_area, ?_⟩
  rw [equalityLowerCylinder_area, equalityUpperCylinder_area]
  ring

theorem weightedCost_zero (d : ℝ) : weightedCost d 0 0 = physicalScale / 8 := by
  rw [weightedCost, DomainArea.unperturbed_domain]
  change physicalScale * (∫ p in baseDomain,
    RuledApproximation.physicalWeight physicalScale ((0 : ℝ) • field d p)) = _
  simp only [zero_smul, RuledApproximation.physicalWeight, PiLp.zero_apply,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, Real.sqrt_one,
    div_one, setIntegral_const, smul_eq_mul, mul_one, RationalEnergy.baseDomain_volume]
  ring

end SlopeRational

end

end OAI
