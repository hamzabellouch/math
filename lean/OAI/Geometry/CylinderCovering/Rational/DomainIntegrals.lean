import OAI.Geometry.CylinderCovering.Rational.Domain
import OAI.Geometry.RuledCovering.Main

namespace OAI

open Set MeasureTheory
noncomputable section

namespace SlopeRational

lemma labelDomain_volume_integral (d ε q : ℝ) :
    volume.real (labelDomain d ε q) =
      ∫ y : ℝ, max ((1 / 2 - 2 * |y|) -
        max (-(1 / 4 : ℝ)) (-ε ^ 2 * ceilingPolynomial d y - q)) 0 := by
  simpa only [Measure.restrict_univ, RuledApproximation.vec2, vec2] using
    RuledApproximation.plane_volume_vertical_interval
      (labelDomain_measurableSet d ε q) (labelDomain_volume_ne_top d ε q)
      (s := Set.univ) MeasurableSet.univ
      (l := fun y => max (-(1 / 4 : ℝ)) (-ε ^ 2 * ceilingPolynomial d y - q))
      (u := fun y => 1 / 2 - 2 * |y|)
      (by intro z; simpa only [mem_univ, true_and] using labelDomain_mem_iff d ε q z)

lemma labelDomain_setIntegral_vertical {d ε q : ℝ} {f : Plane → ℝ}
    (hf : IntegrableOn f (labelDomain d ε q)) :
    (∫ z in labelDomain d ε q, f z) =
      ∫ y : ℝ, ∫ t in Icc
        (max (-(1 / 4 : ℝ)) (-ε ^ 2 * ceilingPolynomial d y - q))
        (1 / 2 - 2 * |y|), f (vec2 y t) := by
  simpa only [Measure.restrict_univ, RuledApproximation.vec2, vec2] using
    RuledApproximation.plane_setIntegral_vertical_interval
      (labelDomain_measurableSet d ε q) hf
      (s := Set.univ) MeasurableSet.univ
      (l := fun y => max (-(1 / 4 : ℝ)) (-ε ^ 2 * ceilingPolynomial d y - q))
      (u := fun y => 1 / 2 - 2 * |y|)
      (by intro z; simpa only [mem_univ, true_and] using labelDomain_mem_iff d ε q z)

end SlopeRational

end

end OAI
