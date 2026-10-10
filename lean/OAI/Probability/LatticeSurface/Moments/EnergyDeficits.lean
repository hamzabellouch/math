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
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.FacetDeficitAnalytic
import OAI.Probability.LatticeSurface.Convexity.FacetQuantile
import OAI.Probability.LatticeSurface.Convexity.GradientWindows
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.ProductVolume
import OAI.Probability.LatticeSurface.Convexity.QuantileCentroid
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.QuantitativeTransport
import OAI.Probability.LatticeSurface.Convexity.RadialExposure
import OAI.Probability.LatticeSurface.Convexity.RetainedBody
import OAI.Probability.LatticeSurface.Convexity.RetainedCoordinates
import OAI.Probability.LatticeSurface.Convexity.RetainedShell
import OAI.Probability.LatticeSurface.Convexity.SliceDensity
import OAI.Probability.LatticeSurface.Convexity.SliceGeometry
import OAI.Probability.LatticeSurface.Convexity.SliceMoments
import OAI.Probability.LatticeSurface.Convexity.SoftThreshold
import OAI.Probability.LatticeSurface.Convexity.WeightedHolder
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality
import OAI.Probability.LatticeSurface.Geometry.BlockAnalytic
import OAI.Probability.LatticeSurface.Geometry.BlockEdgeGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockFacetGeometry
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
import OAI.Probability.LatticeSurface.Moments.AverageCoercivity
import OAI.Probability.LatticeSurface.Moments.CoercivityEnergy
import OAI.Probability.LatticeSurface.Moments.ControlledGradients
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

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

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

end SparseBlocks

noncomputable section

open scoped BigOperators

namespace SparsePaths

attribute [local instance] Classical.propDecidable

end SparsePaths

noncomputable section

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

end SparseWitness

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

end SparseWitness

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

open Filter

open scoped Topology

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

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

noncomputable def blockDeficit (L : ℕ) (h χ : Vertex → ℝ) (z : Vertex) : ℝ :=
  positiveLogVolume L (fun x => h (base L z+x))-
    (positiveLogVolume L (fun x => h (base L z+x)+χ (base L z+x))+
      positiveLogVolume L (fun x => h (base L z+x)-χ (base L z+x)))/2

noncomputable def coarseTail (L : ℕ) (M : ℝ) (χ : Vertex → ℝ) : Vertex → ℝ :=
  fun z => SparseHoles.softThreshold M (χ (base L z+faceCenter L 0))

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

lemma shared_face (L : ℕ) {z w : Vertex} (hzw : SparseHoles.grid.Adj z w) :
    ∃ i j : Fin 4,base L z+faceCenter L i=base L w+faceCenter L j := by
  rcases SparseHoles.adj_cases hzw with rfl|rfl|rfl|rfl
  · refine ⟨1,0,?_⟩;ext <;> simp [base,faceCenter]; ring
  · refine ⟨0,1,?_⟩;ext <;> simp [base,faceCenter]; ring
  · refine ⟨3,2,?_⟩;ext <;> simp [base,faceCenter]; ring
  · refine ⟨2,3,?_⟩;ext <;> simp [base,faceCenter]; ring

lemma coarseTail_pin (L : ℕ) (M : ℝ) (χ : Vertex → ℝ) (z : Vertex)
    (_hM : 0≤M) (hz : |χ (base L z+faceCenter L 0)|≤M) : coarseTail L M χ z=0 := by
  dsimp [coarseTail,SparseHoles.softThreshold]
  rw [max_eq_right (by linarith)]
  simp

lemma tail_face (L : ℕ) (M : ℝ) (χ : Vertex → ℝ) (z : Vertex) (i : Fin 4) (hM : 0≤M) :
    |coarseTail L M χ z-SparseHoles.softThreshold M (χ (base L z+faceCenter L i))| ≤
      |χ (base L z+faceCenter L 0)-χ (base L z+faceCenter L i)| :=
  SparseHoles.softThreshold_lipschitz _ _ _ hM

lemma blockDeficit_nonneg (p : SparseBlocks.Parameters) (h χ : Vertex → ℝ) {z : Vertex}
    (hp : 0<fillingVolume p.L (fun x => h (base p.L z+x)+χ (base p.L z+x)))
    (hm : 0<fillingVolume p.L (fun x => h (base p.L z+x)-χ (base p.L z+x))) :
    0≤blockDeficit p.L h χ z := by
  classical
  have hL : 2≤p.L := by
    have hh := SparseBlocks.L_pos p
    obtain ⟨m,hm⟩ := p.even
    omega
  let r : {x : Vertex // x∈interior p.L} := ⟨(1,1),by simp only [TriangularLipschitz.interior,Finset.mem_product,Finset.mem_Icc];constructor <;> constructor <;> omega⟩
  obtain ⟨n,e,he⟩ := EdgeCoordinates.exists_indexEquiv r
  have hc := positiveLogVolume_concave (EdgeCoordinates.reindex e)
    (EdgeCoordinates.reindex_measurePreserving e) _ _ hp hm
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  have hh : (fun x => (1/2:ℝ)*(h (base p.L z+x)+χ (base p.L z+x))+
      (1/2:ℝ)*(h (base p.L z+x)-χ (base p.L z+x)))=(fun x => h (base p.L z+x)) := by funext x;ring
  rw [hh] at hc
  dsimp [blockDeficit]
  linarith

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

theorem energy_deficits (p : SparseBlocks.Parameters) :
    ∃ C : ℝ,0<C ∧ ∀ (J : Finset Vertex) (h χ : Vertex → ℝ)
      (H : Finset (Finset Vertex)) (N : ℕ) (M : ℝ),0≤M →
      (∀ z∈J,SparseHoles.goodSite H z →
        ConvexGood p.L p.k₀ p.δ p.δ₀ p.s₀ (fun x => h (base p.L z+x))) →
      (∀ z∈J,0<fillingVolume p.L (fun x => h (base p.L z+x)+χ (base p.L z+x))) →
      (∀ z∈J,0<fillingVolume p.L (fun x => h (base p.L z+x)-χ (base p.L z+x))) →
      (∀ z,z∉J → ∀ i : Fin 4,|χ (base p.L z+faceCenter p.L i)|≤M) →
      SparseHoles.goodEnergy H N (coarseTail p.L M χ) ≤
        C*∑ z∈J,blockDeficit p.L h χ z := by
  classical
  obtain ⟨c,hc,hblock⟩ := triangular_block_deficit p.δ p.δ₀ p.s₀ p.k₀ p.L
    p.δpos p.δle p.δ₀le p.klarge p.spos p.even p.Llarge
  refine ⟨8/c,by positivity,?_⟩
  intro J h χ H N M hM hgood hplus hminus hpin
  let g := blockDeficit p.L h χ
  let u := coarseTail p.L M χ
  let a : Vertex → ℝ := fun z => if z∈J then g z else 0
  have hg (z) (hz : z∈J) : 0≤g z := blockDeficit_nonneg p h χ (hplus z hz) (hminus z hz)
  have ha (z) : 0≤a z := by dsimp [a];split_ifs with hz;exact hg z hz;exact le_rfl
  have hface (z : Vertex) (hz : SparseHoles.goodSite H z) (i : Fin 4) :
      c*(u z-SparseHoles.softThreshold M (χ (base p.L z+faceCenter p.L i)))^2≤a z := by
    by_cases hj : z∈J
    · have hb := hblock (fun x => h (base p.L z+x)) (fun x => χ (base p.L z+x))
        (hgood z hj hz) (hplus z hj) (hminus z hj) 0 i
      have ht := tail_face p.L M χ z i hM
      have hsq := sq_le_sq₀ (abs_nonneg _) (abs_nonneg _) |>.mpr ht
      simp only [sq_abs] at hsq hb
      exact (mul_le_mul_of_nonneg_left hsq hc.le).trans (by simpa [a,hj,g,blockDeficit] using hb)
    · have hu : u z=0 := coarseTail_pin _ _ _ _ hM (hpin z hj 0)
      have hf : SparseHoles.softThreshold M (χ (base p.L z+faceCenter p.L i))=0 := by
        dsimp [SparseHoles.softThreshold]
        rw [max_eq_right (by linarith [hpin z hj i])];simp
      simp [a,hj,hu,hf]
  let E := (SparseHoles.incidentEdges (SparseHoles.buffer N)).filter (SparseHoles.goodEdge H)
  have hedge (e : SparseHoles.Edge) (he : e∈E) :
      c*(SparseHoles.edgeAbs u e)^2 ≤
        2*∑ z∈J,if e∈SparseHoles.incidentEdges {z} then g z else 0 := by
    have hegood := (Finset.mem_filter.mp he).2
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : SparseHoles.grid.Adj x y := hegood.1
      have hxg := hegood.2 x (by simp)
      have hyg := hegood.2 y (by simp)
      obtain ⟨i,j,hij⟩ := shared_face p.L hxy
      have hxi := hface x hxg i
      have hyj := hface y hyg j
      rw [← hij] at hyj
      let f := SparseHoles.softThreshold M (χ (base p.L x+faceCenter p.L i))
      have hsq : (u y-u x)^2≤2*((u x-f)^2+(u y-f)^2) := by
        nlinarith [sq_nonneg (u x+u y-2*f)]
      have hbound : c*(u y-u x)^2≤2*(a x+a y) := by
        have hh := mul_le_mul_of_nonneg_left hsq hc.le
        dsimp [f] at hh
        nlinarith
      have hneq : x≠y := SparseHoles.grid.ne_of_adj hxy
      have hs : (∑ z∈J,if s(x,y)∈SparseHoles.incidentEdges {z} then g z else 0)=a x+a y := by
        have hh (z : Vertex) : (if s(x,y)∈SparseHoles.incidentEdges {z} then g z else 0)=
            (if z=x then g z else 0)+(if z=y then g z else 0) := by
          simp only [SparseHoles.mem_incidentEdges,Finset.mem_singleton,exists_eq_left,
            show s(x,y)∈SparseHoles.grid.edgeSet from hxy,true_and,Sym2.mem_iff]
          by_cases hx : z=x <;> by_cases hy : z=y <;> simp_all
        simp_rw [hh]
        rw [Finset.sum_add_distrib]
        simp [a]
      rw [hs,SparseHoles.edgeAbs_mk,sq_abs]
      exact hbound
  have hsum : c*SparseHoles.goodEnergy H N u ≤ 8*∑ z∈J,g z := by
    change c*(∑ e∈E,(SparseHoles.edgeAbs u e)^2)≤_
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ e∈E,2*∑ z∈J,if e∈SparseHoles.incidentEdges {z} then g z else 0 :=
        Finset.sum_le_sum hedge
      _ = 2*∑ z∈J,∑ e∈E,if e∈SparseHoles.incidentEdges {z} then g z else 0 := by
        rw [← Finset.mul_sum,Finset.sum_comm]
      _ ≤ 2*∑ z∈J,4*g z := by
        gcongr with z hz
        simpa using SparseHoles.sum_incident_bound {z} E (g z) (hg z hz)
      _ = 8*∑ z∈J,g z := by rw [← Finset.mul_sum];ring
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hsum)

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

end OAI
