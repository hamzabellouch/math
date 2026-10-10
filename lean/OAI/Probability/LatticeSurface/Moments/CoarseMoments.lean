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
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

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
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

noncomputable section

open scoped BigOperators

namespace SparsePaths

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparsePaths

noncomputable section

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseWitness

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseWitness

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

namespace SparseBlocks

open Filter

open scoped Topology

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

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

theorem actual_coarse_moments (C R : ℝ) (hC : 1≤C) (hR : 1≤R) :
    ∃ p : SparseBlocks.Parameters,∃ a : ℝ,0<a ∧ ∃ M : ℝ≥0,
    ∀ (V : Finset Vertex) (N : ℕ),1≤N → ∀ (w : Vertex → ℝ) (P : Finset Vertex),
    (∑ z∈GridTrace.square N,|w z|)≤C →
    (∀ z∈GridTrace.square N,|w z|≤C/(N:ℝ)^2) → P⊆GridTrace.square N →
    (∀ z∈P,z∉ordinary p V) →
    ((∑ z∈GridTrace.square N,w z)=0 ∨
      ((SparseHoles.star.induce (P:Set Vertex)).Connected ∧ (N:ℝ)≤R*(SparseHoles.diameter P:ℝ))) →
    ∀ lo hi : Vertex,ordinary p V⊆SparseHoles.box lo hi →
    (∫⁻ h,ENNReal.ofReal (Real.exp (a*|coarseFunctional p.L V (ordinary p V) N w
      (split (SparseBlocks.L_pos p) V (ordinary p V) (ordinary_free p V) h).1|)) ∂SparseBlocks.law V)≤M := by
  classical
  obtain ⟨p,T,hT,hdef⟩ := actual_integrated_overlap C R hC hR
  let ρ := (1-Real.exp (-1))/2
  have he : Real.exp (-1)<1 := by rw [← Real.exp_zero];exact Real.exp_lt_exp.mpr (by norm_num)
  have hρ : 0<ρ := by dsimp [ρ];linarith
  have hρ1 : ρ<1 := by dsimp [ρ];linarith [Real.exp_pos (-1)]
  obtain ⟨a,ha,M,hM⟩ := geometric_exponential_moment hT (by linarith : 0≤1-ρ) (by linarith : 1-ρ<1)
  refine ⟨p,a,ha,M,?_⟩
  intro V N hN w P hw hw' hP hP' hanchor lo hi hbox
  let J := ordinary p V
  let d := realDensity p.L V J
  let l := coarseFunctional p.L V J N w
  let F := fun h => (split (SparseBlocks.L_pos p) V J (ordinary_free p V) h).1
  have hF : Measurable F := measurable_fst.comp (split (SparseBlocks.L_pos p) V J (ordinary_free p V)).measurable
  obtain ⟨hdu,hd0,hdl,hde,⟨S,hS,hdK⟩,hdM⟩ := shell_regularity (SparseBlocks.L_pos p) V J (ordinary_free p V)
  have hZ : 0<volume.real (SparseBlocks.body V) :=
    ENNReal.toReal_pos (SparseBlocks.volume_body_positive V).ne' (SparseBlocks.volume_body_finite V)
  have hmass : 0<∫ x,d x := by rw [hdM];exact hZ
  have hdef' : (∫ x,Overlap.overlap d l T S x)≤(1-ρ)*(∫ x,d x) := by
    rw [hdM]
    exact hdef V N hN w P hw hw' hP hP' hanchor lo hi hbox S
  have htail := linear_overlap_geometric_tail l hS hT hρ hρ1 hdu hd0 hdK hde hdl hmass hdef'
  have htail' (j : ℕ) : SparseBlocks.law V {h | (j:ℝ)*T≤|l (F h)|}≤ENNReal.ofReal (1-ρ)^j*SparseBlocks.law V Set.univ := by
    have hBm : MeasurableSet {s | (j:ℝ)*T≤|l s|} :=
      (isClosed_le continuous_const l.continuous.abs).measurableSet
    have hreal := retained_law_real (SparseBlocks.L_pos p) V J (ordinary_free p V) hBm
    have hr : (SparseBlocks.law V).real {h | (j:ℝ)*T≤|l (F h)|}≤(1-ρ)^j := by
      change (SparseBlocks.law V).real ((fun h => (split (SparseBlocks.L_pos p) V J (ordinary_free p V) h).1) ⁻¹' {s | (j:ℝ)*T≤|l s|})≤_
      rw [hreal]
      apply (div_le_iff₀ hZ).mpr
      simpa only [hdM] using htail j
    rw [measure_univ,mul_one,← ENNReal.ofReal_pow (by linarith : 0≤1-ρ)]
    rw [← ENNReal.ofReal_toReal (measure_ne_top (SparseBlocks.law V) _)]
    exact ENNReal.ofReal_le_ofReal hr
  have hm := hM (SparseBlocks.law V) (fun h => l (F h)) (l.continuous.measurable.comp hF) htail'
  simpa only [measure_univ,mul_one] using hm

end RetainedShell

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
