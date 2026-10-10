import OAI.Geometry.CylinderCovering.Rational.TetrahedronGeometryDefinitions
import OAI.Geometry.CylinderCovering.Rational.UncenteredPotentialDefinitions
import OAI.Geometry.CylinderCovering.Rational.DictionaryStatementDefinitions
import OAI.Geometry.CylinderCovering.Rational.UncenteredThresholdDefinitions
import OAI.Geometry.CylinderCovering.Rational.ProductDefinitions
import OAI.Geometry.CylinderCovering.Rational.LogarithmicStatementDefinitions

namespace OAI

noncomputable section
namespace RationalDictionary

def GeometryAndRealizationsStatement : Prop :=
  CoordinateCostStatement ∧
  RationalSimilarity.UncenteredTetrahedronGeometryStatement ∧
  UncenteredStreamStatement ∧
  UncenteredThresholdStatement ∧
  UncenteredCoverageStatement ∧
  SlopeRational.ProductRealizationStatement ∧
  LogarithmicStatement

end RationalDictionary

end

end OAI
