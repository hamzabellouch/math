import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.ConnectedPin
import OAI.Probability.LatticeSurface.Coercivity.DenseSpread
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
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.LinearConcentration
import OAI.Probability.LatticeSurface.Convexity.MarginalBody
import OAI.Probability.LatticeSurface.Convexity.MarginalOverlap
import OAI.Probability.LatticeSurface.Convexity.PointwiseOverlapSupport
import OAI.Probability.LatticeSurface.Convexity.ProductDeficit
import OAI.Probability.LatticeSurface.Convexity.ProductVolume
import OAI.Probability.LatticeSurface.Convexity.QuantileCentroid
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.QuantitativeTransport
import OAI.Probability.LatticeSurface.Convexity.RadialExposure
import OAI.Probability.LatticeSurface.Convexity.RetainedBody
import OAI.Probability.LatticeSurface.Convexity.RetainedCoordinates
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

lemma kernel_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : E → ℝ} (hp0 : ∀ x,0≤p x) (hl : LogConcave p) (x χ : E) :
    Overlap.kernel p x χ≤p x := by
  have hh := hl (x+χ) (x-χ) (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
  have he : (1/2:ℝ) • (x+χ)+(1/2:ℝ) • (x-χ)=x := by module
  simpa only [Overlap.kernel,he,← Real.sqrt_eq_rpow,← Real.sqrt_mul (hp0 _)] using hh

end Density

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

lemma retainedEval_apply (L : ℕ) (V J : Finset Vertex) (x : Vertex) (s : retained L V J → ℝ) :
    retainedEval L V J x s=retainedHeight L V J s x := by
  by_cases hx : x∈retained L V J <;> simp [retainedEval,retainedHeight,hx]

lemma coarseFunctional_apply (L : ℕ) (V J : Finset Vertex) (N : ℕ) (w : Vertex → ℝ)
    (s : retained L V J → ℝ) :
    coarseFunctional L V J N w s=∑ z∈GridTrace.square N,w z*retainedHeight L V J s (base L z+faceCenter L 0) := by
  simp [coarseFunctional,retainedEval_apply]

lemma representative_not_bulk (p : SparseBlocks.Parameters) (J : Finset Vertex) (z : Vertex) :
    base p.L z+faceCenter p.L 0∉bulk p.L J := by
  obtain ⟨m,hm⟩ := p.even
  have hL := SparseBlocks.L_pos p
  have hm0 : 0 < m := by omega
  have he : p.L=2*m := by omega
  have hf := shell_eq_box_not_interior.mp (faceCenter_mem_shell hm0 (0:Fin 4))
  rw [← he] at hf
  exact block_shell_not_bulk hL J z hf.1 hf.2

lemma volume_transfers {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (h : V → ℝ)
    (χ : retained L V J → ℝ) (ψ : Vertex → ℝ)
    (hψ : ∀ x,x∉bulk L J → ψ x=retainedHeight L V J χ x) (z : Vertex) :
    fillingVolume L (fun x => SparseBlocks.height V h (base L z+x))=
      fillingVolume L (shellData L V J (split hL V J hf h).1 z) ∧
    fillingVolume L (fun x => SparseBlocks.height V h (base L z+x)+ψ (base L z+x))=
      fillingVolume L (shellData L V J ((split hL V J hf h).1+χ) z) ∧
    fillingVolume L (fun x => SparseBlocks.height V h (base L z+x)-ψ (base L z+x))=
      fillingVolume L (shellData L V J ((split hL V J hf h).1-χ) z) := by
  have hb (x) (hx : x∈box L) (hi : x∉interior L) := block_shell_not_bulk hL J z hx hi
  refine ⟨?_,?_,?_⟩
  · apply fillingVolume_congr_shell
    intro x hx hi
    exact height_retained hL V J hf h (hb x hx hi)
  · apply fillingVolume_congr_shell
    intro x hx hi
    rw [height_retained hL V J hf h (hb x hx hi),hψ _ (hb x hx hi)]
    exact (retainedHeight_add L V J _ _ _).symm
  · apply fillingVolume_congr_shell
    intro x hx hi
    rw [height_retained hL V J hf h (hb x hx hi),hψ _ (hb x hx hi)]
    exact (retainedHeight_sub L V J _ _ _).symm

lemma deficit_transfer (p : SparseBlocks.Parameters) (V : Finset Vertex)
    (h : V → ℝ) (χ : retained p.L V (ordinary p V) → ℝ) (ψ : Vertex → ℝ)
    (hψ : ∀ x,x∉bulk p.L (ordinary p V) → ψ x=retainedHeight p.L V (ordinary p V) χ x)
    (z : Vertex) : blockDeficit p.L (SparseBlocks.height V h) ψ z=
    shellDeficit p.L V (ordinary p V)
      (split (SparseBlocks.L_pos p) V (ordinary p V) (ordinary_free p V) h).1 χ z := by
  obtain ⟨h0,hp,hm⟩ := volume_transfers (SparseBlocks.L_pos p) V (ordinary p V) (ordinary_free p V) h χ ψ hψ z
  simp only [blockDeficit,shellDeficit,positiveLogVolume,h0,hp,hm]

end RetainedShell

namespace RetainedShell

open TriangularLipschitz MeasureTheory

theorem actual_pointwise_overlap (C R : ℝ) (hC : 1≤C) (hR : 1≤R) :
    ∃ p : SparseBlocks.Parameters,∃ T : ℝ,0<T ∧
    ∀ (V : Finset Vertex) (N : ℕ),1≤N → ∀ (w : Vertex → ℝ) (P : Finset Vertex),
    (∑ z∈GridTrace.square N,|w z|)≤C →
    (∀ z∈GridTrace.square N,|w z|≤C/(N:ℝ)^2) → P⊆GridTrace.square N →
    (∀ z∈P,z∉ordinary p V) →
    ((∑ z∈GridTrace.square N,w z)=0 ∨
      ((SparseHoles.star.induce (P:Set Vertex)).Connected ∧ (N:ℝ)≤R*(SparseHoles.diameter P:ℝ))) →
    ∀ lo hi : Vertex,ordinary p V⊆SparseHoles.box lo hi →
    ∃ G : Set (Finset Vertex),(1/2:ENNReal)≤(SparseBlocks.law V) {h | actualBad p V h∈G} ∧
    ∀ h : V → ℝ,h∈SparseBlocks.body V → actualBad p V h∈G → ∀ S : ℝ,
    Overlap.overlap (realDensity p.L V (ordinary p V))
      (coarseFunctional p.L V (ordinary p V) N w) T S
      (split (SparseBlocks.L_pos p) V (ordinary p V) (ordinary_free p V) h).1 ≤
    Real.exp (-1)*realDensity p.L V (ordinary p V)
      (split (SparseBlocks.L_pos p) V (ordinary p V) (ordinary_free p V) h).1 := by
  classical
  obtain ⟨p,C₀,C₂,hC₀,hC₂,hco⟩ := actual_coercivity C R hC hR
  refine ⟨p,C₀+C₂,by linarith,?_⟩
  intro V N hN w P hw hw' hP hP' hanchor lo hi hbox
  obtain ⟨G,hG,hbound⟩ := hco V N hN w P hw hw' hP hP' hanchor lo hi hbox
  refine ⟨G,hG,?_⟩
  intro h hh hg S
  let J := ordinary p V
  let s := (split (SparseBlocks.L_pos p) V J (ordinary_free p V) h).1
  let d := realDensity p.L V J
  obtain ⟨hdu,hd0,hdl,hde,hdK,hdM⟩ := shell_regularity (SparseBlocks.L_pos p) V J (ordinary_free p V)
  apply Overlap.overlap_le (mul_nonneg (Real.exp_pos _).le (hd0 s))
  intro χ hχ
  by_cases hp : 0<d (s+χ)
  · by_cases hm : 0<d (s-χ)
    · have hs : 0<d s := (Real.sqrt_pos.mpr (mul_pos hp hm)).trans_le (Density.kernel_le hd0 hdl s χ)
      have hpE : 0<shellDensity p.L V J (s+χ) := (ENNReal.toReal_pos_iff.mp hp).1
      have hmE : 0<shellDensity p.L V J (s-χ) := (ENNReal.toReal_pos_iff.mp hm).1
      obtain ⟨ψ,hψ,hψ0,hψr⟩ := feasible_shift_extension (SparseBlocks.L_pos p) V J (ordinary_free p V) s χ hpE hmE
      obtain ⟨hprem,hpv⟩ := positive_density_components (SparseBlocks.L_pos p) V J (ordinary_free p V) (s+χ) hp
      obtain ⟨hmrem,hmv⟩ := positive_density_components (SparseBlocks.L_pos p) V J (ordinary_free p V) (s-χ) hm
      have hpv' (z) (hz : z∈J) : 0<fillingVolume p.L (fun x => SparseBlocks.height V h (base p.L z+x)+ψ (base p.L z+x)) := by
        rw [(volume_transfers (SparseBlocks.L_pos p) V J (ordinary_free p V) h χ ψ hψr z).2.1]
        exact hpv z hz
      have hmv' (z) (hz : z∈J) : 0<fillingVolume p.L (fun x => SparseBlocks.height V h (base p.L z+x)-ψ (base p.L z+x)) := by
        rw [(volume_transfers (SparseBlocks.L_pos p) V J (ordinary_free p V) h χ ψ hψr z).2.2]
        exact hmv z hz
      have hb := hbound h hh hg ψ hψ hψ0 hpv' hmv'
      have hl : (∑ z∈GridTrace.square N,w z*ψ (base p.L z+faceCenter p.L 0))=C₀+C₂ := by
        rw [← hχ.2,coarseFunctional_apply]
        apply Finset.sum_congr rfl
        intro z hz
        rw [hψr _ (representative_not_bulk p J z)]
      rw [hl,abs_of_pos (by linarith : 0<C₀+C₂)] at hb
      let g := ∑ z∈J,blockDeficit p.L (SparseBlocks.height V h) ψ z
      have hg0 : 0≤g := Finset.sum_nonneg fun z hz => blockDeficit_nonneg p _ _ (hpv' z hz) (hmv' z hz)
      have hsqrt : 1≤Real.sqrt g := by rw [Real.sqrt_eq_rpow];dsimp [g,J];nlinarith
      have hg1 : 1≤g := by nlinarith [Real.sq_sqrt hg0,Real.sqrt_nonneg g]
      have hgs : (∑ z∈J,shellDeficit p.L V J s χ z)=g := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (deficit_transfer p V h χ ψ hψr z).symm
      change Real.sqrt (d (s+χ)*d (s-χ))≤Real.exp (-1)*d s
      rw [overlap_product_identity (SparseBlocks.L_pos p) V J (ordinary_free p V) s χ hs hp hm,hgs]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (hd0 s)
    · have hm0 : d (s-χ)=0 := le_antisymm (le_of_not_gt hm) (hd0 _)
      change Real.sqrt (d (s+χ)*d (s-χ))≤_
      rw [hm0,mul_zero,Real.sqrt_zero]
      exact mul_nonneg (Real.exp_pos _).le (hd0 s)
  · have hp0 : d (s+χ)=0 := le_antisymm (le_of_not_gt hp) (hd0 _)
    change Real.sqrt (d (s+χ)*d (s-χ))≤_
    rw [hp0,zero_mul,Real.sqrt_zero]
    exact mul_nonneg (Real.exp_pos _).le (hd0 s)

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

end OAI
