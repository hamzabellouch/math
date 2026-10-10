import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions

namespace OAI

namespace SlopeRational

def EqualityConfigurationStatement : Prop :=
  ∃ C D : RuledApproximation.Cylinder,
    C.axis = RuledApproximation.vec3 1 0 0 ∧
    D.axis = RuledApproximation.vec3 0 1 0 ∧
    C.triangle ∧ D.triangle ∧ IsCompact C.base ∧ IsCompact D.base ∧
    referenceTetrahedron ⊆ C.carrier ∪ D.carrier ∧
    C.area = physicalScale / 8 ∧ D.area = physicalScale / 8 ∧
    C.area + D.area = physicalScale / 4

end SlopeRational

end OAI
