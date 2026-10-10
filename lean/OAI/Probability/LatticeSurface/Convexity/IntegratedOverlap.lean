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
import OAI.Probability.LatticeSurface.Convexity.IntegralDeficit
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.LinearConcentration
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

lemma finite_shellDensity {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (s : retained L V J → ℝ) :
    shellDensity L V J s≠⊤ := by
  let H := retainedBody hL V J hf
  have hH := compact_retainedBody hL V J hf
  have he : Prod.snd '' (H∩Prod.fst ⁻¹' {s})=fiber L V J s := by
    ext a
    constructor
    · rintro ⟨⟨q,b⟩,⟨hb,hq⟩,rfl⟩
      have hqs : q=s := hq
      subst q
      exact (body_fiber hL V J hf s b).mp hb
    · intro ha
      exact ⟨(s,a),⟨(body_fiber hL V J hf s a).mpr ha,rfl⟩,rfl⟩
  change volume (fiber L V J s)≠⊤
  rw [← he]
  exact ((hH.inter_right (isClosed_singleton.preimage continuous_fst)).image continuous_snd).measure_ne_top

lemma ofReal_realDensity {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (s : retained L V J → ℝ) :
    ENNReal.ofReal (realDensity L V J s)=shellDensity L V J s :=
  ENNReal.ofReal_toReal (finite_shellDensity hL V J hf s)

lemma retained_law_real {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V)
    {B : Set (retained L V J → ℝ)} (hB : MeasurableSet B) :
    (SparseBlocks.law V).real ((fun h => (split hL V J hf h).1) ⁻¹' B)=
      (∫ s in B,realDensity L V J s)/volume.real (SparseBlocks.body V) := by
  obtain ⟨hu,h0,hl,he,⟨R,hR,hK⟩,hZ⟩ := shell_regularity hL V J hf
  have hi := Density.integrable_nonneg_usc hu h0 hK
  have hdm : Measurable (shellDensity L V J) := by
    have hh := hu.measurable.ennreal_ofReal
    simpa only [ofReal_realDensity hL V J hf] using hh
  unfold Measure.real
  have hF : Measurable (fun h => (split hL V J hf h).1) := measurable_fst.comp (split hL V J hf).measurable
  rw [← Measure.map_apply (μ:=SparseBlocks.law V) hF hB,
    retained_law hL V J hf,withDensity_apply _ hB]
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const _ hdm]
  have heq : (∫⁻ s in B,shellDensity L V J s)=ENNReal.ofReal (∫ s in B,realDensity L V J s) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi.integrableOn (Filter.Eventually.of_forall h0)]
    exact lintegral_congr fun s => (ofReal_realDensity hL V J hf s).symm
  rw [heq,ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal (integral_nonneg h0)]

lemma law_body_compl (V : Finset Vertex) : SparseBlocks.law V (SparseBlocks.body V)ᶜ=0 := by
  rw [SparseBlocks.law,Measure.smul_apply,Measure.restrict_apply (SparseBlocks.closed_body V).measurableSet.compl]
  simp

end RetainedShell

namespace RetainedShell

open TriangularLipschitz MeasureTheory

theorem actual_integrated_overlap (C R : ℝ) (hC : 1≤C) (hR : 1≤R) :
    ∃ p : SparseBlocks.Parameters,∃ T : ℝ,0<T ∧
    ∀ (V : Finset Vertex) (N : ℕ),1≤N → ∀ (w : Vertex → ℝ) (P : Finset Vertex),
    (∑ z∈GridTrace.square N,|w z|)≤C →
    (∀ z∈GridTrace.square N,|w z|≤C/(N:ℝ)^2) → P⊆GridTrace.square N →
    (∀ z∈P,z∉ordinary p V) →
    ((∑ z∈GridTrace.square N,w z)=0 ∨
      ((SparseHoles.star.induce (P:Set Vertex)).Connected ∧ (N:ℝ)≤R*(SparseHoles.diameter P:ℝ))) →
    ∀ lo hi : Vertex,ordinary p V⊆SparseHoles.box lo hi →
    ∀ S : ℝ,
    (∫ s,Overlap.overlap (realDensity p.L V (ordinary p V))
      (coarseFunctional p.L V (ordinary p V) N w) T S s) ≤
    (1-(1-Real.exp (-1))/2)*volume.real (SparseBlocks.body V) := by
  classical
  obtain ⟨p,T,hT,hpoint⟩ := actual_pointwise_overlap C R hC hR
  refine ⟨p,T,hT,?_⟩
  intro V N hN w P hw hw' hP hP' hanchor lo hi hbox S
  obtain ⟨G,hG,hpoint⟩ := hpoint V N hN w P hw hw' hP hP' hanchor lo hi hbox
  let J := ordinary p V
  let d := realDensity p.L V J
  let l := coarseFunctional p.L V J N w
  let O := Overlap.overlap d l T S
  let F := fun h => (split (SparseBlocks.L_pos p) V J (ordinary_free p V) h).1
  let B := {s | O s≤Real.exp (-1)*d s}
  obtain ⟨hdu,hd0,hdl,hde,⟨U,hU,hdK⟩,hdM⟩ := shell_regularity (SparseBlocks.L_pos p) V J (ordinary_free p V)
  have hOu : UpperSemicontinuous O := Overlap.usc_overlap hdu hd0 l T S
  have hBm : MeasurableSet B := measurableSet_le hOu.measurable (measurable_const.mul hdu.measurable)
  have hF : Measurable F := measurable_fst.comp (split (SparseBlocks.L_pos p) V J (ordinary_free p V)).measurable
  have hgsub : {h | actualBad p V h∈G}⊆F ⁻¹' B∪(SparseBlocks.body V)ᶜ := by
    intro h hg
    by_cases hh : h∈SparseBlocks.body V
    · exact Or.inl (hpoint h hh hg S)
    · exact Or.inr hh
  have hprob : (1/2:ENNReal)≤SparseBlocks.law V (F ⁻¹' B) := by
    calc
      (1/2:ENNReal)≤SparseBlocks.law V {h | actualBad p V h∈G} := hG
      _ ≤ SparseBlocks.law V (F ⁻¹' B∪(SparseBlocks.body V)ᶜ) := measure_mono hgsub
      _ ≤ SparseBlocks.law V (F ⁻¹' B)+SparseBlocks.law V (SparseBlocks.body V)ᶜ := measure_union_le _ _
      _ = SparseBlocks.law V (F ⁻¹' B) := by rw [law_body_compl,add_zero]
  have hprobR : (1/2:ℝ)≤(SparseBlocks.law V).real (F ⁻¹' B) := by
    have hh := ENNReal.toReal_mono (measure_ne_top (SparseBlocks.law V) _) hprob
    simpa only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,Measure.real] using hh
  rw [retained_law_real (SparseBlocks.L_pos p) V J (ordinary_free p V) hBm] at hprobR
  have hZ : 0<volume.real (SparseBlocks.body V) :=
    ENNReal.toReal_pos (SparseBlocks.volume_body_positive V).ne' (SparseBlocks.volume_body_finite V)
  have hm : (∫ s,d s)/2≤∫ s in B,d s := by
    rw [hdM]
    have hh := (le_div_iff₀ hZ).mp hprobR
    linarith
  have hdi : Integrable d := Density.integrable_nonneg_usc hdu hd0 hdK
  have hglo (s) : O s≤d s := Overlap.overlap_le (hd0 s) fun χ hχ => Density.kernel_le hd0 hdl s χ
  have hOi : Integrable O := hdi.mono' hOu.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (Overlap.overlap_nonneg d l T S s)];exact hglo s)
  have hk : Real.exp (-1)≤1 := by rw [← Real.exp_zero];exact Real.exp_le_exp.mpr (by norm_num)
  have hh := Density.integral_deficit hdi hOi hBm hk hd0 hglo (fun s hs => hs) hm
  simpa only [d,hdM] using hh

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
