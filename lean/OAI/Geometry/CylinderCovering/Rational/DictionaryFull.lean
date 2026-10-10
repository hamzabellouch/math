import OAI.Geometry.CylinderCovering.Rational.TetrahedronGeometry
import OAI.Geometry.CylinderCovering.Rational.UncenteredPotential
import OAI.Geometry.CylinderCovering.Rational.DictionaryFullDefinitions
import OAI.Geometry.CylinderCovering.Rational.DictionaryBridge
import OAI.Geometry.CylinderCovering.Rational.UncenteredThreshold
import OAI.Geometry.CylinderCovering.Rational.Product
import OAI.Geometry.CylinderCovering.Rational.LogarithmicPair

namespace OAI

noncomputable section
namespace RationalDictionary

theorem geometry_and_realizations : GeometryAndRealizationsStatement :=
  ⟨coordinate_cost_dictionary, RationalSimilarity.uncenteredTetrahedron_geometry,
    uncentered_stream, uncentered_threshold, uncentered_paired_coverage,
    SlopeRational.product_realization, logarithmic_realization⟩

end RationalDictionary

end

end OAI
