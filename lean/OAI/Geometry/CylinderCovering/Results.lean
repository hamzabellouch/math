import OAI.Geometry.CylinderCovering.Ruled.MotionJacobian
import OAI.Geometry.CylinderCovering.Ruled.BoundaryCertificates
import OAI.Geometry.CylinderCovering.Angular.ZeroTilt
import OAI.Geometry.CylinderCovering.Rational.InverseSum
import OAI.Geometry.CylinderCovering.Ruled.Jacobian
import OAI.Geometry.CylinderCovering.Physical.CapMarginThreshold
import OAI.Geometry.CylinderCovering.Singular.Hessian
import OAI.Geometry.CylinderCovering.Rational.Potential
import OAI.Geometry.CylinderCovering.Caps.FractionalEstimates
import OAI.Geometry.CylinderCovering.Convexity.LevelCrossing
import OAI.Geometry.CylinderCovering.Radial.EqualityCover
import OAI.Geometry.CylinderCovering.Nilpotent.Profile
import OAI.Geometry.CylinderCovering.Simplex.OverlapVolume
import OAI.Geometry.CylinderCovering.Nilpotent.Corollaries
import OAI.Geometry.CylinderCovering.Singular.Stream
import OAI.Geometry.CylinderCovering.Singular.OverlapRemainder
import OAI.Geometry.CylinderCovering.Ruled.EigenframeGeometry
import OAI.Geometry.CylinderCovering.Nilpotent.ApexIdentities
import OAI.Geometry.CylinderCovering.Angular.Construction
import OAI.Geometry.CylinderCovering.Cubic.Profile
import OAI.Geometry.CylinderCovering.Angular.CubicRescaled
import OAI.Geometry.CylinderCovering.Barycentric.ProjectionFactor
import OAI.Geometry.CylinderCovering.Rational.RationalThresholdSource
import OAI.Geometry.CylinderCovering.Convexity.ResidualDisk
import OAI.Geometry.CylinderCovering.Ruled.WeightedCost
import OAI.Geometry.CylinderCovering.Angular.CartesianSelectedCover
import OAI.Geometry.CylinderCovering.Physical.Support
import OAI.Geometry.CylinderCovering.Radial.Regularity
import OAI.Geometry.CylinderCovering.Radial.OverlapQuantitative
import OAI.Geometry.CylinderCovering.Convexity.OrthonormalHeightComparison
import OAI.Geometry.CylinderCovering.Caps.TrapezoidGeometry
import OAI.Geometry.CylinderCovering.Nilpotent.ExceptionalSupport
import OAI.Geometry.CylinderCovering.Ruled.Local
import OAI.Geometry.CylinderCovering.Nilpotent.RateCertificates
import OAI.Geometry.CylinderCovering.Barycentric.Enclosure
import OAI.Geometry.CylinderCovering.Convexity.ConvexBodyShadowBounds
import OAI.Geometry.CylinderCovering.Convexity.ProjectionShapeSupport
import OAI.Geometry.CylinderCovering.Beams.ShapeEquivalence
import OAI.Geometry.CylinderCovering.Angular.TableConsequences
import OAI.Geometry.CylinderCovering.Physical.PaddedFinite
import OAI.Geometry.CylinderCovering.Beams.ProjectionFactor
import OAI.Geometry.CylinderCovering.Rational.OpenSchedules
import OAI.Geometry.CylinderCovering.Convexity.RegularOpenParallelogram
import OAI.Geometry.CylinderCovering.Rational.GlobalDifferential
import OAI.Geometry.CylinderCovering.Rational.GlobalTopology
import OAI.Geometry.CylinderCovering.Angular.DirectBounds
import OAI.Geometry.CylinderCovering.Beams.NeighborhoodSimilarity
import OAI.Geometry.CylinderCovering.Angular.CartesianObstruction
import OAI.Geometry.CylinderCovering.Angular.CartesianRemainder
import OAI.Geometry.CylinderCovering.Radial.ZeroCapSeparation
import OAI.Geometry.CylinderCovering.Physical.CostVariants
import OAI.Geometry.CylinderCovering.Physical.Triangles
import OAI.Geometry.CylinderCovering.Physical.Minimum
import OAI.Geometry.CylinderCovering.Physical.CapNormalized
import OAI.Geometry.CylinderCovering.Angular.SquaredDirect
import OAI.Geometry.CylinderCovering.Radial.UniformApproximation
import OAI.Geometry.CylinderCovering.Radial.Variants
import OAI.Geometry.CylinderCovering.Footprints.Polygon
import OAI.Geometry.CylinderCovering.Rational.EqualityCover
import OAI.Geometry.CylinderCovering.Radial.UniformTags
import OAI.Geometry.CylinderCovering.Footprints.Finite
import OAI.Geometry.CylinderCovering.Caps.Certificates
import OAI.Geometry.CylinderCovering.Physical.CapFinite
import OAI.Geometry.CylinderCovering.Caps.FiniteTheorem
import OAI.Geometry.CylinderCovering.Caps.FiniteShape
import OAI.Geometry.CylinderCovering.Caps.Geometry
import OAI.Geometry.CylinderCovering.Physical.FootprintRate
import OAI.Geometry.CylinderCovering.Rational.Equality
import OAI.Geometry.CylinderCovering.Footprints.QuadraticPhysicalFootprints
import OAI.Geometry.CylinderCovering.Beams.NeighborhoodCovers
import OAI.Geometry.CylinderCovering.Beams.Full
import OAI.Geometry.CylinderCovering.Beams.NeighborhoodFinite
import OAI.Geometry.CylinderCovering.Ruled.LocalEndpoint
import OAI.Geometry.CylinderCovering.Rational.GlobalInversion
import OAI.Geometry.CylinderCovering.Rational.DictionaryFull
import OAI.Geometry.CylinderCovering.Beams.Core
import OAI.Geometry.CylinderCovering.Physical.Finite
import OAI.Geometry.CylinderCovering.Radial.VariantsCore
import OAI.Geometry.CylinderCovering.Footprints.PhysicalConvergence
import OAI.Geometry.CylinderCovering.Angular.Extensions
import OAI.Geometry.CylinderCovering.Singular.Extensions
import OAI.Geometry.CylinderCovering.Physical.Coverage
import OAI.Geometry.CylinderCovering.Rational.DictionaryExpansion
import OAI.Geometry.CylinderCovering.Radial.SqrtActual
import OAI.Geometry.CylinderCovering.Nilpotent.Theorem
import OAI.Geometry.CylinderCovering.Singular.EdgeOneResults
import OAI.Geometry.CylinderCovering.Barycentric.Core
import OAI.Geometry.CylinderCovering.Footprints.Certificates
import OAI.Geometry.CylinderCovering.Convexity.RegularAngularDefinitions
import OAI.Geometry.CylinderCovering.Rational.Construction
import OAI.Geometry.CylinderCovering.Angular.GeneralTheorem
import OAI.Geometry.CylinderCovering.Convexity.RegularBaseVariants
import OAI.Geometry.CylinderCovering.Convexity.OpenParallelogram
import OAI.Geometry.CylinderCovering.Singular.Endpoint
import OAI.Geometry.CylinderCovering.Cartesian.Full
import OAI.Geometry.CylinderCovering.Ruled.Comparison
import OAI.Geometry.CylinderCovering.Rational.RationalThreshold
import OAI.Geometry.CylinderCovering.Ruled.ZeroDiagonal
import OAI.Geometry.CylinderCovering.Nilpotent.Cost
import OAI.Geometry.CylinderCovering.Barycentric.Metric
import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRateTheorem
import OAI.Geometry.TriangularCovering.Main
import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Nilpotent.C1
import OAI.Geometry.CylinderCovering.Ruled.C1Definitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.CylinderCovering.Angular.SharpArea
import OAI.Geometry.CylinderCovering.Ruled.Projection
import OAI.Geometry.CylinderCovering.Angular.CubicTheorem
import OAI.Geometry.CylinderCovering.Angular.CubicMain
import OAI.Geometry.CylinderCovering.Cubic.Contraction
import OAI.Geometry.CylinderCovering.Cubic.ScaledLaws
import OAI.Geometry.CylinderCovering.Radial.Assembly
import OAI.Geometry.CylinderCovering.Radial.ActualEndpoint
import OAI.Geometry.CylinderCovering.Convexity.RegularCounterexamples
import OAI.Geometry.CylinderCovering.Angular.EndpointScaled
import OAI.Geometry.CylinderCovering.Simplex.ProjectionIdentity

namespace OAI

namespace CylinderCovering

theorem triangularHistorical :
    TriangularCovering.A_min = TriangularCovering.H ∧
      TriangularCovering.MainAsymptotic ∧ TriangularCovering.NormalizedCounterexample :=
  TriangularCovering.main

theorem ruledHistorical : RuledApproximation.FullMain :=
  RuledApproximation.fullMain

theorem nilpotentC1 : RuledApproximation.NilpotentC1Statement :=
  RuledApproximation.nilpotentC1

theorem angularExplicit : AngularExplicitStatement :=
  ⟨TriangularCovering.angularArea_result, TriangularCovering.explicitAngular_result⟩

theorem ruledProjection : RuledApproximation.PhysicalProjectionStatement :=
  RuledApproximation.physicalProjection_proof

theorem angularCubic : Cubic.FullCubicStatement := Cubic.fullCubic_proof

theorem radialAligned : RadialSweep.AlignedStatement := RadialSweep.aligned_radial_sweep

theorem radialActualSweep : RadialSweep.ActualSweepStatement :=
  RadialSweep.actual_radial_sweep

theorem regularTriangularCounterexample : RegularTriangularCounterexampleStatement :=
  regularTriangularCounterexample_result

theorem simplexProjectionIdentity : SimplexProjectionIdentityStatement :=
  simplexProjectionIdentity_result

theorem angularEndpoint : AngularEndpointStatement := AngularEndpoint.endpoint_cover

theorem angularEndpointScaled : AngularEndpointScaledStatement :=
  AngularEndpoint.endpoint_scaled_cover

theorem Cubic.scaledMain : Cubic.ScaledMainStatement ∧ Cubic.RescaledFiniteCoverStatement :=
  ⟨Cubic.scaledMain_proof, Cubic.rescaledFiniteCover_proof⟩

theorem regularParallelogramCounterexample : RegularParallelogramCounterexampleStatement :=
  regularParallelogramCounterexample_result

theorem regularOpenCounterexample : RegularOpenCounterexampleStatement :=
  regularOpenCounterexample_result

theorem openParallelogramEnlargement :
    ∀ {n : ℕ} (C : Fin n → RuledApproximation.Cylinder),
      (∀ i, (C i).parallelogram) → ∀ {ε : ℝ}, 0 < ε →
      ∃ D : Fin n → RuledApproximation.Cylinder,
        (∀ i, (D i).axis = (C i).axis) ∧
        (∀ i, (D i).openParallelogram ∧ (D i).openBounded) ∧
        RuledApproximation.familySet C ⊆ RuledApproximation.familySet D ∧
        RuledApproximation.familyArea D < RuledApproximation.familyArea C + ε :=
  by
    intro n C hC ε hε
    exact RuledApproximation.finite_enlarge_openParallelogram (n := n) C hC (ε := ε) hε

theorem singularFlexible : FlexibleSingular.Statement := FlexibleSingular.flexible_singular

theorem cartesianAperture : CartesianFullStatement := CartesianCaps.cartesian_full

theorem ruledComparisons :
    RuledApproximation.SpectralNormComparisonStatement ∧
    RuledApproximation.PhysicalScalingInvarianceStatement ∧
    RuledApproximation.PhysicalNormChangeStatement :=
  ⟨RuledApproximation.spectralNormComparison_proof,
    RuledApproximation.physicalScalingInvariance_proof,
    RuledApproximation.physicalNormChange_proof⟩

theorem rationalThreshold : SlopeRational.ThresholdInclusionStatement :=
  SlopeRational.thresholdInclusion_main

theorem orthogonalZeroDiagonal : RuledApproximation.OrthogonalZeroDiagonalStatement :=
  RuledApproximation.orthogonalZeroDiagonal_proof

theorem nilpotentSaving : Nilpotent.CostSavingStatement := Nilpotent.costSaving_result

theorem barycentricProjection : CylinderBarycentricMetric.ProjectionStatement :=
  CylinderBarycentricMetric.projectionStatement

theorem radialSquareRootCap : RadialSqrtCap.CompleteStatement :=
  RadialSqrtCap.complete_square_root_cap

theorem regularMetricNormalization : RegularMetricNormalizationStatement :=
  regularMetricNormalization_result
theorem angularGeneral : AngularGeneral.Statement := AngularGeneral.general_cap

theorem rationalConstruction : SlopeRational.ConstructionStatement :=
  SlopeRational.construction_main

theorem nilpotentConstruction : Nilpotent.FullConstructionStatement := Nilpotent.fullConstruction

theorem singularEdgeOneDictionary : SingularEdgeOne.DictionaryStatement := SingularEdgeOne.dictionary

theorem barycentricCore : BarycentricCoreStatement := RadialCoordinates.barycentricCore

theorem localFootprintCertificates : Footprints.LocalFootprintCertificates := Footprints.localFootprintCertificates

theorem regularAngularExplicit : RegularExplicitAngularStatement :=
  fun K hK ε hε hsmall => regular_explicit_angular (K := K) (ε := ε) hK hε hsmall

end CylinderCovering

namespace CylinderCovering

theorem rationalDictionaryCoefficients : RationalDictionary.CoefficientLimitsStatement := RationalDictionary.coefficient_limits

theorem rationalDictionaryExpansion : RationalDictionary.UncenteredExpansionStatement := RationalDictionary.uncentered_expansion

end CylinderCovering

namespace CylinderCovering

theorem singularExtensions : SingularExtensionsStatement := singularExtensions_proof

theorem unitEdgeTriangular : UnitEdgeFootprints.FullStatement :=
  UnitEdgeFootprints.full_unit_edge

end CylinderCovering

namespace CylinderCovering

theorem angularExtensions : AngularExtensions.Statement := AngularExtensions.full_extensions

end CylinderCovering

namespace CylinderCovering
theorem nilpotentSmoothRate : NilpotentRate.SmoothRateStatement := NilpotentRate.smoothRate
end CylinderCovering

namespace CylinderCovering

theorem shortenedBeamCosts : BeamCost.CostStatement := BeamCost.fullCost

theorem rationalGlobalInversion : SlopeRational.GlobalWedgeInversionStatement := SlopeRational.globalWedgeInversion_main

theorem ruledProductLocal : ProductLocal.CompleteLocalStatement := ProductLocal.complete_local_proof

theorem ruledProductCellGeometry : ProductCells.GeometryStatement := ProductCells.geometry_proof

theorem rationalDictionary : RationalDictionary.GeometryAndRealizationsStatement :=
  RationalDictionary.geometry_and_realizations

end CylinderCovering

namespace CylinderCovering

theorem beamNeighborhoodAlternative : BeamNeighborhoodRealization.AlternativeStatement :=
  BeamNeighborhoodRealization.alternativeStatement

theorem shortenedBeams : ShortenedBeam.FullStatement := ShortenedBeam.fullConstruction

theorem beamNeighborhoodCounterexamples :
    ShortenedBeam.NeighborhoodMixedStatement ∧ ShortenedBeam.NeighborhoodStrictStatement :=
  ⟨ShortenedBeam.neighborhoodMixedStatement, ShortenedBeam.neighborhoodStrictStatement⟩

end CylinderCovering

namespace CylinderCovering

theorem rationalEquality : SlopeRational.EqualityConfigurationStatement := SlopeRational.equalityConfiguration_main

theorem physicalFootprintCertificates : Footprints.PhysicalFootprintCertificates ∧ PhysicalFootprints.ProjectionShapeStatement := ⟨Footprints.physicalFootprintCertificates, PhysicalFootprints.projection_shapes⟩

end CylinderCovering

namespace CylinderCovering

theorem canonicalFootprintFinite : CanonicalFootprintFinite.Statement := CanonicalFootprintFinite.canonical_footprint_finite

theorem halfheightCertificates : HalfheightCertificates.Statement := HalfheightCertificates.main

theorem physicalCapFinite : RadialPhysical.PhysicalCapCoverageStatement ∧ RadialPhysical.PhysicalCapFiniteStatement := ⟨RadialPhysical.physical_cap_coverage, RadialPhysical.physical_cap_finite⟩

end CylinderCovering

namespace CylinderCovering

theorem absoluteFootprintPolygon : Footprints.AbsolutePolygonStatement := Footprints.absolute_polygon_statement

theorem rationalEqualityCover : SlopeRational.EqualityCover.Statement := SlopeRational.EqualityCover.equality_cover

theorem radialVariants : RadialVariantsStatement := radialVariants_proof

end CylinderCovering

namespace CylinderCovering

theorem physicalCoordinateCosts : RadialPhysical.PhysicalCostVariantsStatement := RadialPhysical.physical_cost_variants

theorem physicalTriangleConstruction : RadialPhysical.ExplicitTriangles.ConstructionStatement := RadialPhysical.ExplicitTriangles.physical_triangle_construction

theorem physicalNormalization : RadialPhysical.PhysicalMinimum.Statement := RadialPhysical.PhysicalMinimum.physical_minimum

theorem physicalCapNormalized : RadialPhysical.PhysicalCapNormalizedStatement := RadialPhysical.physical_cap_normalized

theorem angularSquaredDirect : AngularEstimates.SquaredDirectStatement := AngularEstimates.uniform_squared_direct

theorem radialUniformApproximation : RadialUniformApproximation.Statement := RadialUniformApproximation.uniform_approximation

end CylinderCovering

namespace CylinderCovering
theorem regularBeamNeighborhood : ShortenedBeam.RegularNeighborhoodStatement := ShortenedBeam.regularNeighborhoodStatement
end CylinderCovering

namespace CylinderCovering
theorem rationalOpenSchedules : SlopeRational.OpenPaddingSchedulesStatement := SlopeRational.openPaddingSchedules_main

theorem regularOpenParallelogram : ∀ K : Set Space, IsRegularTetrahedron K → ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder, (∀ i, (C i).openParallelogram ∧ (C i).openBounded) ∧ K ⊆ RuledApproximation.familySet C ∧ RuledApproximation.familyArea C < minimumShadowArea K / 2 ∧ relativeCost K C < 1 / 2 := regularOpenParallelogramCounterexample_result
end CylinderCovering

namespace CylinderCovering
theorem physicalPaddedFinite : RadialPhysical.PhysicalPaddedFiniteStatement := RadialPhysical.physical_padded_finite

theorem beamProjectionFactor : ShortenedBeam.ProjectionFactor.Statement := ShortenedBeam.ProjectionFactor.statement
end CylinderCovering

namespace CylinderCovering
theorem barycentricEnclosure : RadialCoordinates.BarycentricSector.EnclosureStatement :=
  RadialCoordinates.BarycentricSector.enclosureStatement
end CylinderCovering

namespace CylinderCovering
theorem nilpotentSmoothRateCertificates : NilpotentRate.CompleteSmoothRateStatement :=
  NilpotentRate.completeSmoothRate
end CylinderCovering

namespace CylinderCovering
theorem radialOverlapQuantitative : RadialOverlapQuantitative.Statement := RadialOverlapQuantitative.quantitative_overlap

theorem orthonormalHeightCoverage : OrthonormalHeight.CoverageStatement := OrthonormalHeight.cubic_coverage

theorem halfheightGeometry : HalfheightFinite.GeometryStatement := HalfheightFinite.full_halfheight_geometry

end CylinderCovering

end OAI
