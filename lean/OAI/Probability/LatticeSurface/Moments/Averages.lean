import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.ConnectedPin
import OAI.Probability.LatticeSurface.Coercivity.DenseSpread
import OAI.Probability.LatticeSurface.Coercivity.ExponentialTail
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.GridSpreadTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceMain
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleGoodEvent
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleLocal
import OAI.Probability.LatticeSurface.Coercivity.HoleMoments
import OAI.Probability.LatticeSurface.Coercivity.HolePointwise
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HoleTail
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.MomentBuffer
import OAI.Probability.LatticeSurface.Coercivity.MomentMarkov
import OAI.Probability.LatticeSurface.Coercivity.NaturalTailMoments
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Coercivity.PinSpread
import OAI.Probability.LatticeSurface.Coercivity.SparseAmbient
import OAI.Probability.LatticeSurface.Coercivity.SparseClusters
import OAI.Probability.LatticeSurface.Coercivity.SparseColor
import OAI.Probability.LatticeSurface.Coercivity.SparseEntropy
import OAI.Probability.LatticeSurface.Coercivity.SparseGeodesic
import OAI.Probability.LatticeSurface.Coercivity.SparseGeometry
import OAI.Probability.LatticeSurface.Coercivity.SparseGradients
import OAI.Probability.LatticeSurface.Coercivity.SparseModel
import OAI.Probability.LatticeSurface.Coercivity.SparseParameters
import OAI.Probability.LatticeSurface.Coercivity.SparsePaths
import OAI.Probability.LatticeSurface.Coercivity.SparseProb
import OAI.Probability.LatticeSurface.Coercivity.SparseSeparated
import OAI.Probability.LatticeSurface.Coercivity.SparseWitnessModel
import OAI.Probability.LatticeSurface.Coercivity.ThreeEvents
import OAI.Probability.LatticeSurface.Coercivity.TraceCoercivity
import OAI.Probability.LatticeSurface.Coercivity.ZeroPinnedSparse
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.Concentration
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.DensityOverlap
import OAI.Probability.LatticeSurface.Convexity.DensityPrekopa
import OAI.Probability.LatticeSurface.Convexity.EvenIntegral
import OAI.Probability.LatticeSurface.Convexity.FacetDeficitAnalytic
import OAI.Probability.LatticeSurface.Convexity.FacetQuantile
import OAI.Probability.LatticeSurface.Convexity.GeneralMarginal
import OAI.Probability.LatticeSurface.Convexity.GeneralMarginalFin
import OAI.Probability.LatticeSurface.Convexity.GradientWindows
import OAI.Probability.LatticeSurface.Convexity.IntegralDeficit
import OAI.Probability.LatticeSurface.Convexity.IntegratedOverlap
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.LinearConcentration
import OAI.Probability.LatticeSurface.Convexity.LinearCoordinates
import OAI.Probability.LatticeSurface.Convexity.MarginalBody
import OAI.Probability.LatticeSurface.Convexity.MarginalOverlap
import OAI.Probability.LatticeSurface.Convexity.PointwiseOverlap
import OAI.Probability.LatticeSurface.Convexity.PointwiseOverlapSupport
import OAI.Probability.LatticeSurface.Convexity.ProductDeficit
import OAI.Probability.LatticeSurface.Convexity.ProductVolume
import OAI.Probability.LatticeSurface.Convexity.QuantileCentroid
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.QuantitativeTransport
import OAI.Probability.LatticeSurface.Convexity.RadialExposure
import OAI.Probability.LatticeSurface.Convexity.RetainedBody
import OAI.Probability.LatticeSurface.Convexity.RetainedCoordinates
import OAI.Probability.LatticeSurface.Convexity.RetainedLaw
import OAI.Probability.LatticeSurface.Convexity.RetainedShell
import OAI.Probability.LatticeSurface.Convexity.ShellEndpoints
import OAI.Probability.LatticeSurface.Convexity.ShellRegularity
import OAI.Probability.LatticeSurface.Convexity.SliceDensity
import OAI.Probability.LatticeSurface.Convexity.SliceGeometry
import OAI.Probability.LatticeSurface.Convexity.SliceMoments
import OAI.Probability.LatticeSurface.Convexity.SoftThreshold
import OAI.Probability.LatticeSurface.Convexity.Survival
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCGlobal
import OAI.Probability.LatticeSurface.Convexity.USCMarginal
import OAI.Probability.LatticeSurface.Convexity.USCPrekopa
import OAI.Probability.LatticeSurface.Convexity.USCProduct
import OAI.Probability.LatticeSurface.Convexity.Unimodal
import OAI.Probability.LatticeSurface.Convexity.WeightedHolder
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.CompactOverlap
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality
import OAI.Probability.LatticeSurface.Geometry.BlockAnalytic
import OAI.Probability.LatticeSurface.Geometry.BlockEdgeGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockFacetGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockRadial
import OAI.Probability.LatticeSurface.Geometry.BlockTelescope
import OAI.Probability.LatticeSurface.Geometry.BlockVolume
import OAI.Probability.LatticeSurface.Geometry.CapCentral
import OAI.Probability.LatticeSurface.Geometry.CapCompact
import OAI.Probability.LatticeSurface.Geometry.CapContract
import OAI.Probability.LatticeSurface.Geometry.CapCoordinates
import OAI.Probability.LatticeSurface.Geometry.CapMatching
import OAI.Probability.LatticeSurface.Geometry.CapOrient
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapSmall
import OAI.Probability.LatticeSurface.Geometry.CapSplit
import OAI.Probability.LatticeSurface.Geometry.CapUnpin
import OAI.Probability.LatticeSurface.Geometry.CapWeld
import OAI.Probability.LatticeSurface.Geometry.EdgeCoordinates
import OAI.Probability.LatticeSurface.Geometry.FacetBody
import OAI.Probability.LatticeSurface.Geometry.FacetExposure
import OAI.Probability.LatticeSurface.Geometry.TriangularBlock
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry
import OAI.Probability.LatticeSurface.Geometry.UniformFacet
import OAI.Probability.LatticeSurface.Moments.ActualCoercivity
import OAI.Probability.LatticeSurface.Moments.ActualCoercivitySupport
import OAI.Probability.LatticeSurface.Moments.AverageCoercivity
import OAI.Probability.LatticeSurface.Moments.CoarseMoments
import OAI.Probability.LatticeSurface.Moments.CoercivityEnergy
import OAI.Probability.LatticeSurface.Moments.ControlledGradients
import OAI.Probability.LatticeSurface.Moments.EnergyDeficits
import OAI.Probability.LatticeSurface.Moments.OrderedGradients
import OAI.Probability.LatticeSurface.Moments.ScaledEnergy

namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

namespace FacetExposure

end FacetExposure

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

open MeasureTheory Set

open scoped ENNReal

noncomputable section

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

end SliceTransport

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace TriangularLipschitz

end TriangularLipschitz

open scoped BigOperators

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

open Set MeasureTheory Filter

open scoped Topology ENNReal

namespace ExtremalEdges

open scoped ENNReal

end ExtremalEdges

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

noncomputable section

namespace ExtremalEdges

open Finset

variable {V I : Type*} [Fintype V] [Fintype I]

attribute [local instance] Classical.propDecidable

local instance averagesMatchingDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

local instance averagesCapDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

variable {V I : Type*} [Fintype V] [Fintype I]

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

end ExtremalEdges

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance averagesBlocksModelDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

noncomputable section

open scoped BigOperators

namespace SparsePaths

attribute [local instance] Classical.propDecidable

local instance averagesPathsDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparsePaths

noncomputable section

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

local instance averagesWitnessModelDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseWitness

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

local instance averagesWitnessDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseWitness

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance averagesBlocksSeparatedDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance averagesBlocksGradientsDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

open Filter

open scoped Topology

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance averagesBlocksGeometryDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance averagesBlocksAmbientDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance averagesBlocksGeodesicDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace ProductVolume

universe u v

variable {ι : Type u} [Fintype ι] {J : ι → Type v} [∀ i, Fintype (J i)]

end ProductVolume

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace SparseBlocks

end SparseBlocks

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

noncomputable section

open scoped BigOperators

namespace GridClosedLabels

end GridClosedLabels

namespace GridClosedLabels

end GridClosedLabels

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

open scoped BigOperators

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

open Classical

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

attribute [local instance] Classical.propDecidable

end SparseHoles

open scoped BigOperators

namespace SparseHoles

end SparseHoles

noncomputable section

open scoped BigOperators

namespace GridTrace

namespace NatGrid

end NatGrid

end GridTrace

namespace GridTrace.NatGrid

end GridTrace.NatGrid

namespace GridTrace.NatGrid

end GridTrace.NatGrid

namespace GridTrace.NatGrid

end GridTrace.NatGrid

noncomputable section

open scoped BigOperators

namespace GridTrace

end GridTrace

namespace GridTrace

end GridTrace

namespace GridTrace.NatGrid

end GridTrace.NatGrid

noncomputable section

open scoped BigOperators

namespace GridTrace

end GridTrace

namespace SparseHoles

end SparseHoles

namespace SparseHoles

attribute [local instance] Classical.propDecidable

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace GridTrace

end GridTrace

namespace GridTrace

end GridTrace

namespace GridTrace

end GridTrace

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

open Set MeasureTheory

namespace SparseClusters

variable {V : Type*} [Fintype V] [DecidableEq V]

end SparseClusters

namespace SparseClusters

variable {V : Type*} [Fintype V] [DecidableEq V]

end SparseClusters

namespace SparseHoles

open MeasureTheory

end SparseHoles

namespace SparseHoles

open MeasureTheory

attribute [local instance] Classical.propDecidable

end SparseHoles

namespace SparseHoles

open MeasureTheory

attribute [local instance] Classical.propDecidable

end SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

end SparseHoles

namespace SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

end SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

end SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

end SparseHoles

namespace SparseHoles

open MeasureTheory

open scoped ENNReal NNReal

end SparseHoles

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace TriangularLipschitz

end TriangularLipschitz

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace SparseBlocks

open MeasureTheory

end SparseBlocks

namespace RetainedShell

open TriangularLipschitz MeasureTheory

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace RetainedShell

open TriangularLipschitz MeasureTheory

end RetainedShell

open Set Filter

open scoped Topology NNReal

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

end Overlap

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Density

namespace FacetVolume

end FacetVolume

namespace Overlap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

end Overlap

namespace FacetVolume

end FacetVolume

namespace Density

open FacetVolume

end Density

namespace Density

end Density

namespace Density

end Density

namespace Density

end Density

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace RetainedDensity

end RetainedDensity

namespace RetainedDensity

open MeasureTheory

end RetainedDensity

namespace FacetVolume

end FacetVolume

namespace RetainedDensity

open MeasureTheory

end RetainedDensity

open scoped NNReal ENNReal

namespace Density

open MeasureTheory

end Density

namespace RetainedDensity

end RetainedDensity

namespace RetainedShell

open TriangularLipschitz MeasureTheory

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace Density

end Density

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz MeasureTheory

end RetainedShell

namespace RetainedShell

open TriangularLipschitz MeasureTheory

end RetainedShell

namespace Density

open MeasureTheory Set

end Density

namespace RetainedShell

open TriangularLipschitz MeasureTheory Set

end RetainedShell

namespace RetainedShell

open TriangularLipschitz MeasureTheory

end RetainedShell

open scoped ENNReal NNReal

open MeasureTheory Measure

namespace Overlap

open MeasureTheory Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]

end Overlap

open scoped ENNReal NNReal

open MeasureTheory Set

open MeasureTheory Set

open scoped NNReal ENNReal

noncomputable section

namespace RetainedShell

open TriangularLipschitz MeasureTheory

end RetainedShell

open scoped NNReal

namespace MacroscopicAverages

open SparseBlocks

attribute [local instance] Classical.propDecidable

noncomputable def coordinateBox (lo hi : Vertex) : Finset Vertex :=
  Finset.Icc lo.1 hi.1 ×ˢ Finset.Icc lo.2 hi.2

def statistic (V : Finset Vertex) (q : Vertex →₀ ℝ) (h : V → ℝ) : ℝ :=
  q.sum (fun x t => t*height V h x)

end MacroscopicAverages

namespace MacroscopicAverages

open TriangularLipschitz MeasureTheory

attribute [local instance] Classical.propDecidable

noncomputable def cell (L : ℕ) (x : Vertex) : Vertex := (x.1/(L:ℤ),x.2/(L:ℤ))

noncomputable def cellSites (L : ℕ) (z : Vertex) : Finset Vertex :=
  Finset.Ico ((L:ℤ)*z.1) ((L:ℤ)*z.1+L) ×ˢ Finset.Ico ((L:ℤ)*z.2) ((L:ℤ)*z.2+L)

noncomputable def weight (L : ℕ) (q : Vertex →₀ ℝ) (z : Vertex) : ℝ :=
  ∑ x∈q.support with cell L x=z,q x

lemma cell_remainder {L : ℕ} (hL : 0<L) (x : Vertex) :
    x-RetainedShell.base L (cell L x)∈box L := by
  have hLi : (0:ℤ)<L := by exact_mod_cast hL
  have h1 := Int.emod_nonneg x.1 hLi.ne'
  have h2 := Int.emod_nonneg x.2 hLi.ne'
  have h3 := Int.emod_lt_of_pos x.1 hLi
  have h4 := Int.emod_lt_of_pos x.2 hLi
  have he1 := Int.mul_ediv_add_emod x.1 (L:ℤ)
  have he2 := Int.mul_ediv_add_emod x.2 (L:ℤ)
  simp only [mem_box,Prod.fst_sub,Prod.snd_sub,RetainedShell.base,cell]
  constructor <;> constructor <;> nlinarith

lemma mem_cellSites {L : ℕ} (hL : 0<L) (x : Vertex) : x∈cellSites L (cell L x) := by
  have hLi : (0:ℤ)<L := by exact_mod_cast hL
  have h1 := Int.emod_nonneg x.1 hLi.ne'
  have h2 := Int.emod_nonneg x.2 hLi.ne'
  have h3 := Int.emod_lt_of_pos x.1 hLi
  have h4 := Int.emod_lt_of_pos x.2 hLi
  have he1 := Int.mul_ediv_add_emod x.1 (L:ℤ)
  have he2 := Int.mul_ediv_add_emod x.2 (L:ℤ)
  simp only [cellSites,Finset.mem_product,Finset.mem_Ico,cell]
  constructor <;> constructor <;> nlinarith

lemma card_cellSites (L : ℕ) (z : Vertex) : (cellSites L z).card=L^2 := by
  simp [cellSites,Int.card_Ico,pow_two]

lemma cell_mem_square {L N : ℕ} (hL : 0<L) (x : Vertex)
    (hx : 0≤x.1 ∧ x.1≤(L:ℤ)*N ∧ 0≤x.2 ∧ x.2≤(L:ℤ)*N) :
    cell L x∈GridTrace.square N := by
  have hLi : (0:ℤ)<L := by exact_mod_cast hL
  have ha := Int.ediv_le_ediv hLi hx.2.1
  have hb := Int.ediv_le_ediv hLi hx.2.2.2
  rw [Int.mul_ediv_cancel_left _ hLi.ne'] at ha hb
  simp only [GridTrace.square,Finset.mem_product,Finset.mem_Icc,cell]
  exact ⟨⟨Int.ediv_nonneg hx.1 hLi.le,ha⟩,Int.ediv_nonneg hx.2.2.1 hLi.le,hb⟩

lemma sum_weight (L N : ℕ) (q : Vertex →₀ ℝ)
    (hs : ∀ x∈q.support,cell L x∈GridTrace.square N) (f : Vertex → ℝ) :
    (∑ z∈GridTrace.square N,weight L q z*f z)=q.sum (fun x t => t*f (cell L x)) := by
  classical
  calc
    _ = ∑ z∈GridTrace.square N,∑ x∈q.support with cell L x=z,q x*f (cell L x) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [weight,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hs _

lemma sum_weight_abs (L N : ℕ) (q : Vertex →₀ ℝ)
    (hs : ∀ x∈q.support,cell L x∈GridTrace.square N) :
    (∑ z∈GridTrace.square N,|weight L q z|)≤q.sum (fun _ t => |t|) := by
  classical
  exact (Finset.sum_le_sum fun z hz => Finset.abs_sum_le_sum_abs _ _).trans_eq
    (Finset.sum_fiberwise_of_maps_to hs _)

lemma weight_bound {L : ℕ} (hL : 0<L) (q : Vertex →₀ ℝ) {d : ℝ}
    (hd : 0≤d) (hq : ∀ x,|q x|≤d) (z : Vertex) : |weight L q z|≤(L:ℝ)^2*d := by
  classical
  have hc : (q.support.filter (fun x => cell L x=z)).card≤L^2 := by
    rw [← card_cellSites L z]
    apply Finset.card_le_card
    intro x hx
    rw [← (Finset.mem_filter.mp hx).2]
    exact mem_cellSites hL x
  calc
    _ ≤ ∑ x∈q.support with cell L x=z,|q x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x∈q.support with cell L x=z,d := Finset.sum_le_sum fun x hx => hq x
    _ = ((q.support.filter (fun x => cell L x=z)).card:ℝ)*d := by simp
    _ ≤ (L:ℝ)^2*d := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hd

lemma representative_close {L : ℕ} (hL : 0<L) (x : Vertex) :
    latticeDist x (RetainedShell.base L (cell L x)+faceCenter L 0)≤2*(L:ℝ) := by
  have hf := RetainedShell.face_in_box L 0
  have hx := cell_remainder hL x
  have he : x=RetainedShell.base L (cell L x)+(x-RetainedShell.base L (cell L x)) := by abel
  conv_lhs => arg 1; rw [he]
  rw [latticeDist_add_left]
  exact latticeDist_box_le hx hf

lemma representative_error {L N : ℕ} (hL : 0<L) (q : Vertex →₀ ℝ)
    (hs : ∀ x∈q.support,cell L x∈GridTrace.square N)
    (h : Vertex → ℝ) (hh : ∀ x y,Adj x y → |h x-h y|≤1) :
    |q.sum (fun x t => t*h x)-∑ z∈GridTrace.square N,weight L q z*h (RetainedShell.base L z+faceCenter L 0)|≤
      2*(L:ℝ)*q.sum (fun _ t => |t|) := by
  rw [sum_weight L N q hs]
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x∈q.support,|q x| *|h x-h (RetainedShell.base L (cell L x)+faceCenter L 0)| := by
      simpa only [← mul_sub,abs_mul] using Finset.abs_sum_le_sum_abs (fun x => q x*h x-q x*h (RetainedShell.base L (cell L x)+faceCenter L 0)) q.support
    _ ≤ ∑ x∈q.support,|q x| *(2*(L:ℝ)) := Finset.sum_le_sum fun x hx =>
      mul_le_mul_of_nonneg_left ((global_lipschitz h hh _ _).trans (representative_close hL x)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul];ring

end MacroscopicAverages

namespace MacroscopicAverages

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

lemma ediv_adj {L : ℕ} (hL : 0<L) {a b : ℤ} (h : (a-b).natAbs≤1) :
    (a/(L:ℤ)-b/(L:ℤ)).natAbs≤1 := by
  have hLi : (0:ℤ)<L := by exact_mod_cast hL
  have hab : a≤b+L := by omega
  have hba : b≤a+L := by omega
  have ha := Int.ediv_le_ediv hLi hab
  have hb := Int.ediv_le_ediv hLi hba
  rw [Int.add_ediv_of_dvd_right (dvd_refl (L:ℤ)),Int.ediv_self hLi.ne'] at ha hb
  omega

lemma adj_cell {L : ℕ} (hL : 0<L) {x y : Vertex} (h : Adj x y) :
    cell L x=cell L y ∨ SparseHoles.star.Adj (cell L x) (cell L y) := by
  by_cases he : cell L x=cell L y
  · exact Or.inl he
  apply Or.inr
  refine ⟨he,?_,?_⟩
  · apply ediv_adj hL
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · apply ediv_adj hL
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> simp

lemma connected_image_stutter {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    (P : Finset α) (f : α → β) [DecidableEq β]
    (hc : (G.induce (P:Set α)).Connected)
    (hf : ∀ x y,G.Adj x y → f x=f y ∨ H.Adj (f x) (f y)) :
    (H.induce (P.image f:Set β)).Connected := by
  let F : P → P.image f := fun x => ⟨f x,Finset.mem_image.mpr ⟨x,x.property,rfl⟩⟩
  have sur : Function.Surjective F := by
    rintro ⟨y,hy⟩
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨⟨x,hx⟩,rfl⟩
  have hF (x y : P) (hxy : (G.induce (P:Set α)).Adj x y) :
      (H.induce (P.image f:Set β)).Reachable (F x) (F y) := by
    rcases hf x y hxy with he|ha
    · have he' : F x=F y := Subtype.ext he
      rw [he']
    · exact SimpleGraph.Adj.reachable ha
  have : Nonempty (P.image f) := by
    obtain ⟨x⟩ := hc.nonempty
    exact ⟨F x⟩
  constructor
  intro x y
  obtain ⟨a,rfl⟩ := sur x
  obtain ⟨b,rfl⟩ := sur y
  rw [SimpleGraph.reachable_iff_reflTransGen]
  apply Relation.ReflTransGen.lift' F (fun x y hxy => ?_) a b (by
    simpa only [SimpleGraph.reachable_iff_reflTransGen] using hc a b)
  simpa only [SimpleGraph.reachable_iff_reflTransGen] using hF x y hxy

lemma anchor_connected {L : ℕ} (hL : 0<L) (P : Finset Vertex)
    (hc : (latticeGraph.induce (P:Set Vertex)).Connected) :
    (SparseHoles.star.induce (P.image (cell L):Set Vertex)).Connected :=
  connected_image_stutter latticeGraph SparseHoles.star P (cell L) hc (fun _ _ => adj_cell hL)

lemma pin_cell_not_ordinary (p : SparseBlocks.Parameters) (V : Finset Vertex)
    (x : Vertex) (hx : x∉V) : cell p.L x∉RetainedShell.ordinary p V := by
  intro ho
  have hm := RetainedShell.ordinary_free p V _ ho _ (cell_remainder (SparseBlocks.L_pos p) x)
  have he : RetainedShell.base p.L (cell p.L x)+(x-RetainedShell.base p.L (cell p.L x))=x := by abel
  rw [he] at hm
  exact hx hm

lemma anchor_diameter {L : ℕ} (hL : 0<L) (P : Finset Vertex) (x : Vertex) (hx : x∈P)
    (y : Vertex) (hy : y∈P) :
    latticeDist x y≤2*(L:ℝ)*(SparseHoles.diameter (P.image (cell L)):ℝ)+4*L := by
  have ha := SparseHoles.le_diameter (P.image (cell L))
    (Finset.mem_image.mpr ⟨x,hx,rfl⟩) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
  have h1 : |((cell L x).1:ℝ)-(cell L y).1|≤(SparseHoles.diameter (P.image (cell L)):ℝ) := by
    have hh : ((((cell L x).1-(cell L y).1).natAbs:ℕ):ℝ)≤(SparseHoles.diameter (P.image (cell L)):ℝ) := by exact_mod_cast ha.1
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,Int.cast_sub] at hh
    exact hh
  have h2 : |((cell L x).2:ℝ)-(cell L y).2|≤(SparseHoles.diameter (P.image (cell L)):ℝ) := by
    have hh : ((((cell L x).2-(cell L y).2).natAbs:ℕ):ℝ)≤(SparseHoles.diameter (P.image (cell L)):ℝ) := by exact_mod_cast ha.2
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,Int.cast_sub] at hh
    exact hh
  have hc : latticeDist (RetainedShell.base L (cell L x)+faceCenter L 0)
      (RetainedShell.base L (cell L y)+faceCenter L 0)≤2*(L:ℝ)*(SparseHoles.diameter (P.image (cell L)):ℝ) := by
    have he1 : ((RetainedShell.base L (cell L x)+faceCenter L 0).1:ℝ)-
        (RetainedShell.base L (cell L y)+faceCenter L 0).1=(L:ℝ)*(((cell L x).1:ℝ)-(cell L y).1) := by
      simp [RetainedShell.base];ring
    have he2 : ((RetainedShell.base L (cell L x)+faceCenter L 0).2:ℝ)-
        (RetainedShell.base L (cell L y)+faceCenter L 0).2=(L:ℝ)*(((cell L x).2:ℝ)-(cell L y).2) := by
      simp [RetainedShell.base];ring
    have hl : (0:ℝ)≤L := Nat.cast_nonneg _
    have hd : (0:ℝ)≤SparseHoles.diameter (P.image (cell L)) := Nat.cast_nonneg _
    rw [latticeDist,he1,he2]
    have hh1 := mul_le_mul_of_nonneg_left h1 hl
    have hh2 := mul_le_mul_of_nonneg_left h2 hl
    rw [← abs_of_nonneg hl,← abs_mul] at hh1 hh2
    simp only [abs_of_nonneg hl] at hh1 hh2
    have hh3 := abs_add_le ((L:ℝ)*(((cell L x).1:ℝ)-(cell L y).1)) ((L:ℝ)*(((cell L x).2:ℝ)-(cell L y).2))
    exact max_le (max_le (by nlinarith) (by nlinarith)) (by nlinarith)
  have ht := latticeDist_triangle x (RetainedShell.base L (cell L x)+faceCenter L 0) y
  have ht' := latticeDist_triangle (RetainedShell.base L (cell L x)+faceCenter L 0)
    (RetainedShell.base L (cell L y)+faceCenter L 0) y
  have hx' := representative_close hL x
  have hy' := representative_close hL y
  rw [latticeDist_comm] at hy'
  linarith

end MacroscopicAverages

namespace MacroscopicAverages

open SparseBlocks MeasureTheory

attribute [local instance] Classical.propDecidable

lemma continuous_statistic (V : Finset Vertex) (q : Vertex →₀ ℝ) : Continuous (statistic V q) := by
  apply continuous_finsetSum
  intro x hx
  exact continuous_const.mul (continuous_height V x)

lemma law_ae_body (V : Finset Vertex) : ∀ᵐ h∂law V,h∈body V := by
  rw [ae_iff]
  exact RetainedShell.law_body_compl V

lemma deterministic_statistic (V : Finset Vertex) (q : Vertex →₀ ℝ) (h : V → ℝ)
    (hh : h∈body V) (x : Vertex) {D : ℝ}
    (hx : q.sum (fun _ t => t)=0 ∨ x∉V)
    (hD : ∀ y∈q.support,latticeDist y x≤D) :
    |statistic V q h|≤D*q.sum (fun _ t => |t|) := by
  have he : statistic V q h=q.sum (fun y t => t*(height V h y-height V h x)) := by
    simp only [statistic,Finsupp.sum,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
    rcases hx with hz|hx
    · change q.sum (fun y t => t*height V h y)=q.sum (fun y t => t*height V h y)-q.sum (fun _ t => t)*height V h x
      rw [hz,zero_mul,sub_zero]
    · simp [height,hx]
  rw [he]
  calc
    _ ≤ ∑ y∈q.support,|q y| *|height V h y-height V h x| := by
      simpa only [Finsupp.sum,abs_mul] using Finset.abs_sum_le_sum_abs (fun y => q y*(height V h y-height V h x)) q.support
    _ ≤ ∑ y∈q.support,|q y| *D := Finset.sum_le_sum fun y hy =>
      mul_le_mul_of_nonneg_left ((TriangularLipschitz.global_lipschitz _ hh y x).trans (hD y hy)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul];simp only [Finsupp.sum];ring

lemma nonnegative_distance {D : ℝ} (x y : Vertex)
    (hx : 0≤(x.1:ℝ) ∧ (x.1:ℝ)≤D ∧ 0≤(x.2:ℝ) ∧ (x.2:ℝ)≤D)
    (hy : 0≤(y.1:ℝ) ∧ (y.1:ℝ)≤D ∧ 0≤(y.2:ℝ) ∧ (y.2:ℝ)≤D) : latticeDist x y≤2*D := by
  have hd : 0≤D := hx.1.trans hx.2.1
  have h1 : |(x.1:ℝ)-y.1|≤D := abs_le.mpr ⟨by linarith,by linarith⟩
  have h2 : |(x.2:ℝ)-y.2|≤D := abs_le.mpr ⟨by linarith,by linarith⟩
  exact max_le (max_le (by linarith) (by linarith)) ((abs_add_le _ _).trans (by linarith))

lemma mgf_transfer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    {a D : ℝ} (ha : 0≤a) (hg : Measurable g) (he : ∀ᵐ x∂μ,|f x-g x|≤D) :
    (∫⁻ x,ENNReal.ofReal (Real.exp (a*|f x|)) ∂μ)≤
      ENNReal.ofReal (Real.exp (a*D))*(∫⁻ x,ENNReal.ofReal (Real.exp (a*|g x|)) ∂μ) := by
  calc
    _ ≤ ∫⁻ x,ENNReal.ofReal (Real.exp (a*D))*ENNReal.ofReal (Real.exp (a*|g x|)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [he] with x hx
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hab : |f x|≤|f x-g x|+|g x| := by
        calc
          _ = |(f x-g x)+g x| := by rw [sub_add_cancel]
          _ ≤ _ := abs_add_le _ _
      have h : |f x|≤D+|g x| := by linarith
      nlinarith
    _ = _ := lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hg.abs)))

lemma mgf_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) {a D : ℝ} (ha : 0≤a) (he : ∀ᵐ x∂μ,|f x|≤D) :
    (∫⁻ x,ENNReal.ofReal (Real.exp (a*|f x|)) ∂μ)≤ENNReal.ofReal (Real.exp (a*D)) := by
  calc
    _ ≤ ∫⁻ x,ENNReal.ofReal (Real.exp (a*D)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [he] with x hx
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ha))
    _ = _ := by simp

lemma finite_in_box (S : Finset Vertex) : ∃ lo hi : Vertex,S⊆SparseHoles.box lo hi := by
  let N := S.sup (fun x => max x.1.natAbs x.2.natAbs)
  refine ⟨(-(N:ℤ),-(N:ℤ)),((N:ℤ),(N:ℤ)),?_⟩
  intro x hx
  have hd : max x.1.natAbs x.2.natAbs≤N := Finset.le_sup (f := fun x : Vertex => max x.1.natAbs x.2.natAbs) hx
  have h1 : x.1.natAbs≤N := (le_max_left _ _).trans hd
  have h2 : x.2.natAbs≤N := (le_max_right _ _).trans hd
  simp only [SparseHoles.box,Finset.mem_product,Finset.mem_Icc]
  constructor <;> omega

lemma coarseFunctional_height (p : Parameters) (V : Finset Vertex) (N : ℕ) (w : Vertex → ℝ) (h : V → ℝ) :
    RetainedShell.coarseFunctional p.L V (RetainedShell.ordinary p V) N w
      (RetainedShell.split (L_pos p) V (RetainedShell.ordinary p V) (RetainedShell.ordinary_free p V) h).1=
      ∑ z∈GridTrace.square N,w z*height V h (RetainedShell.base p.L z+TriangularLipschitz.faceCenter p.L 0) := by
  rw [RetainedShell.coarseFunctional_apply]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← RetainedShell.height_retained (L_pos p) V (RetainedShell.ordinary p V)
    (RetainedShell.ordinary_free p V) h (RetainedShell.representative_not_bulk p _ z)]

end MacroscopicAverages

namespace MacroscopicAverages

lemma coarse_scale {C R c : ℝ} {L : ℕ} (hC : 0<C) (hc : 0<c) (hL : 0<L)
    (hR : (L:ℝ)≤R) (hcR : 8*(L:ℝ)≤c*R) :
    ∃ N : ℕ,1≤N ∧ C*R≤(L:ℝ)*N ∧ (N:ℝ)≤(C+2)*R/(L:ℝ) ∧
    (L:ℝ)^2*(C*R^(-2:ℤ))≤(C*(C+2)^2)/(N:ℝ)^2 ∧
    ∀ d : ℕ,c*R≤2*(L:ℝ)*d+4*L → (N:ℝ)≤(4*(C+2)/c)*(d:ℝ) := by
  have hl : (0:ℝ)<L := by exact_mod_cast hL
  have hr : 0<R := hl.trans_le hR
  let N := ⌈C*R/(L:ℝ)⌉₊+1
  have hn : 1≤N := Nat.le_add_left _ _
  have hn' : (0:ℝ)<N := by exact_mod_cast hn
  have he := Nat.le_ceil (C*R/(L:ℝ))
  have he' := Nat.ceil_lt_add_one (le_of_lt (div_pos (mul_pos hC hr) hl))
  have heN : (N:ℝ)≤C*R/(L:ℝ)+2 := by
    dsimp [N];push_cast;linarith
  have hNR : (N:ℝ)≤(C+2)*R/(L:ℝ) := by
    apply heN.trans
    apply (le_div_iff₀ hl).mpr
    rw [add_mul,div_mul_cancel₀ _ hl.ne']
    nlinarith
  refine ⟨N,hn,?_,hNR,?_,?_⟩
  · have h := mul_le_mul_of_nonneg_left he hl.le
    rw [mul_div_cancel₀ _ hl.ne'] at h
    have hn0 : (⌈C*R/(L:ℝ)⌉₊:ℝ)≤N := by dsimp [N];push_cast;linarith
    exact h.trans (mul_le_mul_of_nonneg_left hn0 hl.le)
  · have hNR' : (N:ℝ)*(L:ℝ)≤(C+2)*R := (le_div_iff₀ hl).mp hNR
    have hs := sq_le_sq₀ (by positivity : 0≤(N:ℝ)*(L:ℝ)) (by positivity : 0≤(C+2)*R) |>.mpr hNR'
    rw [zpow_neg,zpow_ofNat]
    apply (le_div_iff₀ (sq_pos_of_pos hn')).mpr
    rw [← div_eq_mul_inv]
    have heq : (L:ℝ)^2*(C/R^2)*(N:ℝ)^2=(C*((N:ℝ)*(L:ℝ))^2)/R^2 := by ring
    rw [heq]
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs hC.le]
  · intro d hd
    have hd' : c*R≤4*(L:ℝ)*d := by linarith
    apply hNR.trans
    apply (div_le_iff₀ hl).mpr
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd' (by linarith : 0≤C+2)]

end MacroscopicAverages

namespace MacroscopicAverages

open SparseBlocks MeasureTheory

open scoped NNReal

attribute [local instance] Classical.propDecidable

theorem nonnegative_moments (c C : ℝ) (hc : 0<c) (hC : 0<C) :
    ∃ a : ℝ,0<a ∧ ∃ M : ℝ≥0,∀ (V : Finset Vertex) (R : ℝ),1≤R →
    ∀ q : Vertex →₀ ℝ,
    (∀ x∈q.support,0≤(x.1:ℝ) ∧ (x.1:ℝ)≤C*R ∧ 0≤(x.2:ℝ) ∧ (x.2:ℝ)≤C*R) →
    q.sum (fun _ t => |t|)≤C → (∀ x,|q x|≤C*R^(-2:ℤ)) →
    ((q.sum (fun _ t => t))=0 ∨ ∃ P : Finset Vertex,
      (∀ x∈P,0≤(x.1:ℝ) ∧ (x.1:ℝ)≤C*R ∧ 0≤(x.2:ℝ) ∧ (x.2:ℝ)≤C*R) ∧ Disjoint P V ∧
      (TriangularLipschitz.latticeGraph.induce (P:Set Vertex)).Connected ∧
      ∃ x∈P,∃ y∈P,c*R≤latticeDist x y) →
    (∫⁻ h,ENNReal.ofReal (Real.exp (a*|statistic V q h|)) ∂law V)≤M := by
  classical
  let CC := max 1 (max C (C*(C+2)^2))
  let RR := max 1 (4*(C+2)/c)
  have hCC : 1≤CC := le_max_left _ _
  have hCC' : C≤CC := (le_max_left _ _).trans (le_max_right _ _)
  have hCC'' : C*(C+2)^2≤CC := (le_max_right _ _).trans (le_max_right _ _)
  have hRR : 1≤RR := le_max_left _ _
  obtain ⟨p,a,ha,M,hM⟩ := RetainedShell.actual_coarse_moments CC RR hCC hRR
  let S : ℝ := max (p.L:ℝ) (8*(p.L:ℝ)/c)
  let E : ℝ := 2*(p.L:ℝ)*C
  let D : ℝ := 2*C^2*S
  let ME : ℝ≥0 := ⟨Real.exp (a*E),(Real.exp_pos _).le⟩
  let MD : ℝ≥0 := ⟨Real.exp (a*D),(Real.exp_pos _).le⟩
  refine ⟨a,ha,ME*M+MD,?_⟩
  intro V R hR q hqs hq1 hq2 hanchor
  have hl : (0:ℝ)<p.L := by exact_mod_cast L_pos p
  have hr : 0<R := lt_of_lt_of_le zero_lt_one hR
  by_cases hlarge : S≤R
  · have hRL : (p.L:ℝ)≤R := (le_max_left _ _).trans hlarge
    have hcR : 8*(p.L:ℝ)≤c*R := by
      have hh : 8*(p.L:ℝ)/c≤R := (le_max_right _ _).trans hlarge
      exact (div_le_iff₀ hc).mp hh |>.trans_eq (mul_comm R c)
    obtain ⟨N,hN,hscale,hscale',hweight,hdiam⟩ := coarse_scale hC hc (L_pos p) hRL hcR
    have hsall (x : Vertex) (hx : 0≤(x.1:ℝ) ∧ (x.1:ℝ)≤C*R ∧ 0≤(x.2:ℝ) ∧ (x.2:ℝ)≤C*R) :
        cell p.L x∈GridTrace.square N := by
      apply cell_mem_square (L_pos p)
      refine ⟨by exact_mod_cast hx.1,?_,by exact_mod_cast hx.2.2.1,?_⟩
      · exact_mod_cast hx.2.1.trans hscale
      · exact_mod_cast hx.2.2.2.trans hscale
    have hs : ∀ x∈q.support,cell p.L x∈GridTrace.square N := fun x hx => hsall x (hqs x hx)
    let w := weight p.L q
    have hw : (∑ z∈GridTrace.square N,|w z|)≤CC := (sum_weight_abs p.L N q hs).trans (hq1.trans hCC')
    have hw' (z) (hz : z∈GridTrace.square N) : |w z|≤CC/(N:ℝ)^2 := by
      apply (weight_bound (L_pos p) q (by positivity) hq2 z).trans
      exact hweight.trans (div_le_div_of_nonneg_right hCC'' (sq_nonneg _))
    obtain ⟨P,hP,hPv,hPa⟩ : ∃ P : Finset Vertex,P⊆GridTrace.square N ∧
        (∀ z∈P,z∉RetainedShell.ordinary p V) ∧
        ((∑ z∈GridTrace.square N,w z)=0 ∨
        ((SparseHoles.star.induce (P:Set Vertex)).Connected ∧ (N:ℝ)≤RR*(SparseHoles.diameter P:ℝ))) := by
      rcases hanchor with hz|⟨P,hPc,hPv,hPc',x,hx,y,hy,hxy⟩
      · refine ⟨∅,Finset.empty_subset _,by simp,Or.inl ?_⟩
        have he := sum_weight p.L N q hs (fun _ => 1)
        simpa only [mul_one,w,hz] using he
      · refine ⟨P.image (cell p.L),?_,?_,Or.inr ⟨anchor_connected (L_pos p) P hPc',?_⟩⟩
        · intro z hz
          obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
          exact hsall x (hPc x hx)
        · intro z hz
          obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
          exact pin_cell_not_ordinary p V x (Finset.disjoint_left.mp hPv hx)
        · have hd := hdiam _ (hxy.trans (anchor_diameter (L_pos p) P x hx y hy))
          exact hd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))
    obtain ⟨lo,hi,hbox⟩ := finite_in_box (RetainedShell.ordinary p V)
    let g : (V → ℝ) → ℝ := fun h => ∑ z∈GridTrace.square N,w z*height V h (RetainedShell.base p.L z+TriangularLipschitz.faceCenter p.L 0)
    have hgm : Measurable g := by
      apply Continuous.measurable
      apply continuous_finsetSum
      intro z hz
      exact continuous_const.mul (continuous_height V _)
    have hm : (∫⁻ h,ENNReal.ofReal (Real.exp (a*|g h|)) ∂law V)≤M := by
      simpa only [coarseFunctional_height] using hM V N hN w P hw hw' hP hPv hPa lo hi hbox
    have herr : ∀ᵐ h∂law V,|statistic V q h-g h|≤E := by
      filter_upwards [law_ae_body V] with h hh
      have he := representative_error (L_pos p) q hs (height V h) hh
      exact he.trans (mul_le_mul_of_nonneg_left hq1 (by positivity))
    have hm' := (mgf_transfer (law V) (statistic V q) g ha.le hgm herr).trans (mul_le_mul_of_nonneg_left hm (by positivity))
    change (∫⁻ h,ENNReal.ofReal (Real.exp (a*|statistic V q h|)) ∂law V)≤↑(ME*M+MD)
    have he : ENNReal.ofReal (Real.exp (a*E))=(ME:ENNReal) := by
      exact ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le
    rw [he] at hm'
    exact hm'.trans (by simp only [ENNReal.coe_add,ENNReal.coe_mul];exact le_add_of_nonneg_right (by positivity))
  · have hRS : R≤S := le_of_not_ge hlarge
    have herr : ∀ᵐ h∂law V,|statistic V q h|≤D := by
      filter_upwards [law_ae_body V] with h hh
      by_cases hqz : q=0
      · have hS : 0≤S := hr.le.trans hRS
        simp only [statistic,hqz,Finsupp.sum_zero_index,abs_zero]
        dsimp [D]
        positivity
      have hn : q.support.Nonempty := Finsupp.support_nonempty_iff.mpr hqz
      obtain ⟨x,hx,hanchor'⟩ : ∃ x,(0≤(x.1:ℝ) ∧ (x.1:ℝ)≤C*R ∧ 0≤(x.2:ℝ) ∧ (x.2:ℝ)≤C*R) ∧
          (q.sum (fun _ t => t)=0 ∨ x∉V) := by
        rcases hanchor with hz|⟨P,hPc,hPv,hPc',x,hx,y,hy,hxy⟩
        · obtain ⟨x,hx⟩ := hn
          exact ⟨x,hqs x hx,Or.inl hz⟩
        · exact ⟨x,hPc x hx,Or.inr (Finset.disjoint_left.mp hPv hx)⟩
      have hb := deterministic_statistic V q h hh x hanchor' (fun y hy => nonnegative_distance y x (hqs y hy) hx)
      apply hb.trans
      have hCR : 0≤2*(C*R) := by positivity
      have hb' := mul_le_mul_of_nonneg_left hq1 hCR
      have hb'' := mul_le_mul_of_nonneg_left hRS (by positivity : 0≤2*C^2)
      dsimp [D]
      nlinarith
    have hm := mgf_bounded (law V) (statistic V q) ha.le herr
    have he : ENNReal.ofReal (Real.exp (a*D))=(MD:ENNReal) := by
      exact ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le
    rw [he] at hm
    exact hm.trans (by simp only [ENNReal.coe_add];exact le_add_of_nonneg_left (by positivity))

end MacroscopicAverages

namespace MacroscopicAverages

open SparseBlocks MeasureTheory

attribute [local instance] Classical.propDecidable

noncomputable def shift (a : Vertex) : Vertex ↪ Vertex := ⟨fun x => x-a,fun _ _ h => sub_left_injective h⟩

noncomputable def shifted (a : Vertex) (V : Finset Vertex) : Finset Vertex := V.image (shift a)

lemma mem_shifted (a : Vertex) (V : Finset Vertex) (x : Vertex) : x-a∈shifted a V ↔ x∈V := by
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    have he' : y=x := (shift a).injective he
    rwa [he'] at hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

noncomputable def shiftIndex (a : Vertex) (V : Finset Vertex) : V ≃ shifted a V where
  toFun x := ⟨x-a,(mem_shifted a V x).mpr x.property⟩
  invFun y := ⟨y+a,by
    apply (mem_shifted a V (y+a)).mp
    simp⟩
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp

noncomputable def shiftHeights (a : Vertex) (V : Finset Vertex) : (V → ℝ) ≃ᵐ (shifted a V → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shiftIndex a V)

lemma shiftHeights_apply (a : Vertex) (V : Finset Vertex) (h : V → ℝ) (x : V) :
    shiftHeights a V h (shiftIndex a V x)=h x := by
  simp [shiftHeights,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft_apply_eq_cast]

lemma height_shift (a : Vertex) (V : Finset Vertex) (h : V → ℝ) (x : Vertex) :
    height (shifted a V) (shiftHeights a V h) (x-a)=height V h x := by
  by_cases hx : x∈V
  · have hx' := (mem_shifted a V x).mpr hx
    simpa only [height,dite_eq_left hx',dite_eq_left hx] using (show shiftHeights a V h ⟨x-a,hx'⟩=h ⟨x,hx⟩ from shiftHeights_apply a V h ⟨x,hx⟩)
  · simp [height,hx,(mem_shifted a V x).not.mpr hx]

lemma shift_body (a : Vertex) (V : Finset Vertex) :
    shiftHeights a V ⁻¹' body (shifted a V)=body V := by
  ext h
  constructor
  · intro hh x y hxy
    have ha := hh (x-a) (y-a) ((adj_sub x y a).mpr hxy)
    simpa only [height_shift] using ha
  · intro hh x y hxy
    have ha := hh (x+a) (y+a) ((adj_sub (x+a) (y+a) a).mp (by simpa using hxy))
    simpa only [← height_shift a V h,add_sub_cancel_right] using ha

lemma preserving_shift_law (a : Vertex) (V : Finset Vertex) :
    MeasurePreserving (shiftHeights a V) (law V) (law (shifted a V)) := by
  have hp : MeasurePreserving (shiftHeights a V) := volume_measurePreserving_piCongrLeft _ (shiftIndex a V)
  have hm := hp.measure_preimage (closed_body (shifted a V)).measurableSet.nullMeasurableSet
  rw [shift_body] at hm
  have hr := (hp.restrict_preimage (closed_body (shifted a V)).measurableSet).smul_measure (volume (body V))⁻¹
  simpa only [shift_body,hm,law] using hr

lemma latticeDist_shift (a x y : Vertex) : latticeDist (x-a) (y-a)=latticeDist x y := by
  have h1 : ((x-a).1:ℝ)-(y-a).1=(x.1:ℝ)-y.1 := by simp
  have h2 : ((x-a).2:ℝ)-(y-a).2=(x.2:ℝ)-y.2 := by simp
  simp only [latticeDist,h1,h2]

lemma shifted_disjoint (a : Vertex) (P V : Finset Vertex) (hd : Disjoint P V) :
    Disjoint (shifted a P) (shifted a V) := by
  apply Finset.disjoint_left.mpr
  intro x hx hv
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact (Finset.disjoint_left.mp hd hy) ((mem_shifted a V y).mp hv)

end MacroscopicAverages

namespace MacroscopicAverages

open SparseBlocks

theorem zero_pinned_exponential_moments (c C : ℝ) (hc : 0<c) (hC : 0<C) :
    ∃ a : ℝ,0<a ∧ ∃ M : ℝ≥0,∀ (V : Finset Vertex) (R : ℝ),1≤R →
    ∀ (lo hi : Vertex) (q : Vertex →₀ ℝ),
    q.support ⊆ coordinateBox lo hi →
    (∀ x∈coordinateBox lo hi,∀ y∈coordinateBox lo hi,latticeDist x y≤C*R) →
    q.sum (fun _ t => |t|)≤C → (∀ x,|q x|≤C*R^(-2:ℤ)) →
    ((q.sum (fun _ t => t))=0 ∨ ∃ P : Finset Vertex,
      P⊆coordinateBox lo hi ∧ Disjoint P V ∧
      (TriangularLipschitz.latticeGraph.induce (P:Set Vertex)).Connected ∧
      ∃ x∈P,∃ y∈P,c*R≤latticeDist x y) →
    (∫⁻ h,ENNReal.ofReal (Real.exp (a*|statistic V q h|)) ∂law V)≤M := by
  classical
  obtain ⟨a,ha,M,hM⟩ := nonnegative_moments c C hc hC
  refine ⟨a,ha,M+1,?_⟩
  intro V R hR lo hi q hqs hdiam hq1 hq2 hanchor
  by_cases hqz : q=0
  · simp [statistic,hqz]
  have hne : q.support.Nonempty := Finsupp.support_nonempty_iff.mpr hqz
  obtain ⟨x,hx⟩ := hne
  have hb := hqs hx
  have hlo : lo∈coordinateBox lo hi := by
    simp only [coordinateBox,Finset.mem_product,Finset.mem_Icc] at hb ⊢
    exact ⟨⟨le_rfl,hb.1.1.trans hb.1.2⟩,le_rfl,hb.2.1.trans hb.2.2⟩
  have hcoord (y : Vertex) (hy : y∈coordinateBox lo hi) :
      0≤((y-lo).1:ℝ) ∧ ((y-lo).1:ℝ)≤C*R ∧ 0≤((y-lo).2:ℝ) ∧ ((y-lo).2:ℝ)≤C*R := by
    have hd := hdiam y hy lo hlo
    have hb := hy
    simp only [coordinateBox,Finset.mem_product,Finset.mem_Icc] at hb
    have h1 : 0≤(y.1:ℝ)-lo.1 := sub_nonneg.mpr (by exact_mod_cast hb.1.1)
    have h2 : 0≤(y.2:ℝ)-lo.2 := sub_nonneg.mpr (by exact_mod_cast hb.2.1)
    have hd1 : |(y.1:ℝ)-lo.1|≤C*R := ((le_max_left _ _).trans (le_max_left _ _)).trans hd
    have hd2 : |(y.2:ℝ)-lo.2|≤C*R := ((le_max_right _ _).trans (le_max_left _ _)).trans hd
    simpa only [Prod.fst_sub,Prod.snd_sub,Int.cast_sub] using
      And.intro h1 (And.intro ((le_abs_self _).trans hd1) (And.intro h2 ((le_abs_self _).trans hd2)))
  let V' := shifted lo V
  let q' := q.embDomain (shift lo)
  have hqs' : ∀ x∈q'.support,0≤(x.1:ℝ) ∧ (x.1:ℝ)≤C*R ∧ 0≤(x.2:ℝ) ∧ (x.2:ℝ)≤C*R := by
    intro x hx
    rw [Finsupp.support_embDomain] at hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
    exact hcoord y (hqs hy)
  have hq1' : q'.sum (fun _ t => |t|)≤C := by
    simpa only [q',Finsupp.sum_embDomain] using hq1
  have hq2' (x : Vertex) : |q' x|≤C*R^(-2:ℤ) := by
    have he : shift lo (x+lo)=x := by change (x+lo)-lo=x; abel
    rw [← he,Finsupp.embDomain_apply_self]
    exact hq2 _
  have hanchor' : (q'.sum (fun _ t => t))=0 ∨ ∃ P : Finset Vertex,
      (∀ x∈P,0≤(x.1:ℝ) ∧ (x.1:ℝ)≤C*R ∧ 0≤(x.2:ℝ) ∧ (x.2:ℝ)≤C*R) ∧ Disjoint P V' ∧
      (TriangularLipschitz.latticeGraph.induce (P:Set Vertex)).Connected ∧
      ∃ x∈P,∃ y∈P,c*R≤latticeDist x y := by
    rcases hanchor with hz|⟨P,hP,hPv,hPc,x,hx,y,hy,hxy⟩
    · exact Or.inl (by simpa only [q',Finsupp.sum_embDomain] using hz)
    · apply Or.inr
      refine ⟨shifted lo P,?_,shifted_disjoint lo P V hPv,?_,x-lo,(mem_shifted lo P x).mpr hx,y-lo,(mem_shifted lo P y).mpr hy,?_⟩
      · intro z hz
        obtain ⟨y,hy,he⟩ := Finset.mem_image.mp (show z∈P.image (shift lo) from hz)
        rw [← he]
        exact hcoord y (hP hy)
      · exact connected_image_stutter TriangularLipschitz.latticeGraph TriangularLipschitz.latticeGraph P
          (shift lo) hPc (fun x y hxy => Or.inr ((adj_sub x y lo).mpr hxy))
      · rwa [latticeDist_shift]
  have hm := hM V' R hR q' hqs' hq1' hq2' hanchor'
  have he (h : V → ℝ) : statistic V' q' (shiftHeights lo V h)=statistic V q h := by
    change (q.embDomain (shift lo)).sum _=q.sum _
    rw [Finsupp.sum_embDomain]
    unfold Finsupp.sum
    apply Finset.sum_congr rfl
    intro y hy
    change q y*height (shifted lo V) (shiftHeights lo V h) (y-lo)=q y*height V h y
    rw [height_shift]
  have hmp := preserving_shift_law lo V
  have hlint := hmp.lintegral_comp (f := fun h => ENNReal.ofReal (Real.exp (a*|statistic V' q' h|))) (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (continuous_statistic V' q').measurable.abs)))
  rw [← hlint] at hm
  simp only [he] at hm
  exact hm.trans (by simp only [ENNReal.coe_add,ENNReal.coe_one];exact le_add_of_nonneg_right (by positivity))

end MacroscopicAverages

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
