import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseAmbient
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
import OAI.Probability.LatticeSurface.Coercivity.ZeroPinnedSparse
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.GradientWindows
import OAI.Probability.LatticeSurface.Convexity.ProductVolume
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.RetainedCoordinates
import OAI.Probability.LatticeSurface.Convexity.RetainedShell
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality
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
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry
import OAI.Probability.LatticeSurface.Moments.ControlledGradients
import OAI.Probability.LatticeSurface.Moments.OrderedGradients

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

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

local instance retainedLawMatchingDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

local instance retainedLawCapDecidableEq (carrier : Sort*) : DecidableEq carrier :=
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

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

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

local instance retainedLawBlocksModelDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

noncomputable section

open scoped BigOperators

namespace SparsePaths

attribute [local instance] Classical.propDecidable

local instance retainedLawPathsDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparsePaths

noncomputable section

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

local instance retainedLawWitnessModelDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseWitness

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

local instance retainedLawWitnessDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseWitness

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance retainedLawBlocksSeparatedDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance retainedLawBlocksGradientsDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

open Filter

open scoped Topology

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance retainedLawBlocksGeometryDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance retainedLawBlocksAmbientDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance retainedLawBlocksGeodesicDecidableEq (carrier : Sort*) : DecidableEq carrier :=
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

namespace RetainedShell

open TriangularLipschitz

theorem retained_law {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) :
    Measure.map (fun h => (split hL V J hf h).1) (SparseBlocks.law V) =
      volume.withDensity (fun s => shellDensity L V J s / volume (SparseBlocks.body V)) := by
  classical
  let e := split hL V J hf
  let H := e.symm ⁻¹' SparseBlocks.body V
  have hH : MeasurableSet H := e.symm.measurable (SparseBlocks.closed_body V).measurableSet
  have hslice (s : retained L V J → ℝ) : Prod.mk s ⁻¹' H=fiber L V J s := by
    ext a;exact body_fiber hL V J hf s a
  have hd : Measurable (shellDensity L V J) := by
    have hh := measurable_measure_prodMk_left (ν:=(volume:Measure (J→Filling L))) hH
    change Measurable (fun s => volume (fiber L V J s))
    simpa only [hslice] using hh
  apply Measure.ext
  intro S hS
  change (Measure.map (Prod.fst ∘ e) (SparseBlocks.law V)) S =
    (volume.withDensity (fun s => shellDensity L V J s / volume (SparseBlocks.body V))) S
  rw [Measure.map_apply (measurable_fst.comp e.measurable) hS,withDensity_apply _ hS]
  rw [SparseBlocks.law,Measure.smul_apply,Measure.restrict_apply (measurable_fst.comp e.measurable hS)]
  change (volume (SparseBlocks.body V))⁻¹*volume (_∩_)=_
  let T := H∩Prod.fst ⁻¹' S
  have hT : MeasurableSet T := hH.inter (measurable_fst hS)
  have heT : e ⁻¹' T = (Prod.fst ∘ e) ⁻¹' S∩SparseBlocks.body V := by
    ext h
    simp only [T,H,Function.comp_apply,Set.mem_preimage,Set.mem_inter_iff,MeasurableEquiv.symm_apply_apply]
    tauto
  rw [← heT,(preserving_split hL V J hf).measure_preimage_emb e.measurableEmbedding T]
  have hvol : volume T=∫⁻ s in S,shellDensity L V J s := by
    change (volume.prod volume) T=_
    rw [Measure.prod_apply hT,← lintegral_indicator hS]
    apply lintegral_congr
    intro s
    by_cases hs : s∈S
    · have he : Prod.mk s ⁻¹' T=Prod.mk s ⁻¹' H := by ext a;simp [T,hs]
      rw [he,hslice,Set.indicator_of_mem hs]
      rfl
    · have he : Prod.mk s ⁻¹' T=∅ := by ext a;simp [T,hs]
      simp [he,hs]
  rw [hvol]
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const _ hd]
  exact mul_comm _ _

end RetainedShell

end
end
end
end
end
end
end

end OAI
