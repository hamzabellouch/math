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
import OAI.Probability.LatticeSurface.Convexity.AnchoredCoupling
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
import OAI.Probability.LatticeSurface.Moments.Averages
import OAI.Probability.LatticeSurface.Moments.CoercivityEnergy
import OAI.Probability.LatticeSurface.Moments.ControlledGradients
import OAI.Probability.LatticeSurface.Moments.EnergyDeficits
import OAI.Probability.LatticeSurface.Moments.OrderedGradients
import OAI.Probability.LatticeSurface.Moments.ScaledEnergy

namespace OAI

noncomputable section

namespace BoundedLattice

open Set MeasureTheory SparseBlocks

attribute [local instance] Classical.propDecidable

def height (V : Finset Vertex) (b : Vertex → ℝ) (h : V → ℝ) (x : Vertex) : ℝ :=
  if hx : x∈V then h ⟨x,hx⟩ else b x

def body (V : Finset Vertex) (b : Vertex → ℝ) : Set (V → ℝ) :=
  {h | ∀ x∈V,∀ y,Adj x y → |height V b h x-height V b h y|≤1}

noncomputable def law (V : Finset Vertex) (b : Vertex → ℝ) : Measure (V → ℝ) :=
  (volume (body V b))⁻¹ • volume.restrict (body V b)

def statistic (V : Finset Vertex) (b : Vertex → ℝ) (q : Vertex →₀ ℝ) (h : V → ℝ) : ℝ :=
  q.sum (fun x t => t*height V b h x)

end BoundedLattice

namespace BoundedData

open Set

attribute [local instance] Classical.propDecidable

def activeGraph {V : Type*} (G : SimpleGraph V) (pins : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x∉pins ∨ y∉pins)
  symm := ⟨by intro x y h; exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1.ne rfl⟩

lemma activeGraph_anchored {V : Type*} (G : SimpleGraph V) (hc : G.Connected)
    (pins : Set V) (hp : pins.Nonempty) :
    ∀ x : V,∃ p∈pins,(activeGraph G pins).Reachable x p := by
  intro x
  obtain ⟨p,hp⟩ := hp
  obtain ⟨w⟩ := hc x p
  induction w with
  | nil => exact ⟨_,hp,SimpleGraph.Reachable.refl _⟩
  | @cons x y p hxy w ih =>
    by_cases hx : x∈pins
    · exact ⟨x,hx,SimpleGraph.Reachable.refl _⟩
    · obtain ⟨q,hq,hr⟩ := ih hp
      exact ⟨q,hq,(show (activeGraph G pins).Adj x y from ⟨hxy,Or.inl hx⟩).reachable.trans hr⟩

end BoundedData

namespace BoundedLattice

open Set MeasureTheory SparseBlocks ExtremalEdges

attribute [local instance] Classical.propDecidable

lemma continuous_height (V : Finset Vertex) (b : Vertex → ℝ) (x : Vertex) :
    Continuous (fun h => height V b h x) := by
  by_cases hx : x∈V
  · simpa [height,hx] using (continuous_apply (⟨x,hx⟩ : V) : Continuous (fun h : V → ℝ => h ⟨x,hx⟩))
  · simpa [height,hx] using (continuous_const : Continuous (fun _ : V → ℝ => b x))

lemma closed_body (V : Finset Vertex) (b : Vertex → ℝ) : IsClosed (body V b) := by
  simp only [body,ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_le ((continuous_height V b x).sub (continuous_height V b y)).abs continuous_const

lemma body_zero (V : Finset Vertex) : body V (fun _ => 0)=SparseBlocks.body V := by
  ext h
  constructor
  · intro hh x y hxy
    by_cases hx : x∈V
    · exact hh x hx y hxy
    · by_cases hy : y∈V
      · simpa only [height,SparseBlocks.height,abs_sub_comm] using hh y hy x (adj_symm hxy)
      · simp [SparseBlocks.height,hx,hy]
  · intro hh x hx y hxy
    exact hh x y hxy

lemma law_zero (V : Finset Vertex) : law V (fun _ => 0)=SparseBlocks.law V := by
  simp only [law,SparseBlocks.law,body_zero]

lemma statistic_zero (V : Finset Vertex) (q : Vertex →₀ ℝ) (h : V → ℝ) :
    statistic V (fun _ => 0) q h=MacroscopicAverages.statistic V q h := rfl

lemma coordinates_height (A V : Finset Vertex) (hVA : V⊆A)
    (b : Vertex → ℝ) (h : V → ℝ) (x : A) :
    restore (fixed A V) (fun x : A => b x.val) (coordinates A V hVA h) x=height V b h x.val := by
  by_cases hx : x.val∈V
  · have hxp : x∉fixed A V := by simpa [fixed] using hx
    rw [restore,dite_eq_right hxp,height,dite_eq_left hx]
    change (Equiv.piCongrLeft (fun _ : Free (fixed A V) => ℝ) (indexEquiv A V hVA)) h
      ⟨x,hxp⟩=h ⟨x.val,hx⟩
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  · simp [restore,fixed,height,hx]

lemma body_coordinates (A V : Finset Vertex) (hVA : V⊆A)
    (hcollar : ∀ x∈V,∀ y,Adj x y → y∈A) (b : Vertex → ℝ) :
    (coordinates A V hVA) ⁻¹' conditionalBody (BoundedData.activeGraph (finiteGraph A) (fixed A V))
      (fixed A V) (fun x : A => b x.val)=body V b := by
  ext h
  constructor
  · intro hh x hx y hxy
    have hyA := hcollar x hx y hxy
    have he : (BoundedData.activeGraph (finiteGraph A) (fixed A V)).Adj ⟨x,hVA hx⟩ ⟨y,hyA⟩ :=
      ⟨hxy,Or.inl (by simpa [fixed] using hx)⟩
    have hb := hh ⟨x,hVA hx⟩ ⟨y,hyA⟩ he
    simpa only [coordinates_height] using hb
  · intro hh x y hxy
    rw [coordinates_height,coordinates_height]
    rcases hxy.2 with hx | hy
    · exact hh x.val (by simpa [fixed] using hx) y.val hxy.1
    · simpa only [abs_sub_comm] using hh y.val (by simpa [fixed] using hy) x.val (adj_symm hxy.1)

lemma map_law (A V : Finset Vertex) (hVA : V⊆A)
    (hcollar : ∀ x∈V,∀ y,Adj x y → y∈A) (b : Vertex → ℝ) :
    Measure.map (coordinates A V hVA) (law V b)=
      BoundedData.law (BoundedData.activeGraph (finiteGraph A) (fixed A V)) (fixed A V) (fun x : A => b x.val) := by
  let K := conditionalBody (BoundedData.activeGraph (finiteGraph A) (fixed A V)) (fixed A V) (fun x : A => b x.val)
  have hK : MeasurableSet K := (closed_conditionalBody _ _ _).measurableSet
  have he : (coordinates A V hVA) ⁻¹' K=body V b := body_coordinates A V hVA hcollar b
  have hv : volume (body V b)=volume K := by
    rw [← he]
    exact (preserving_coordinates A V hVA).measure_preimage hK.nullMeasurableSet
  rw [law,Measure.map_smul _ (coordinates A V hVA).measurable.aemeasurable,hv,← he]
  rw [← Measure.restrict_map (coordinates A V hVA).measurable hK]
  rw [(preserving_coordinates A V hVA).map_eq]
  rfl

end BoundedLattice

namespace BoundedLattice

open Set MeasureTheory SparseBlocks ExtremalEdges

attribute [local instance] Classical.propDecidable

lemma inverse_map_law (A V : Finset Vertex) (hVA : V⊆A)
    (hcollar : ∀ x∈V,∀ y,Adj x y → y∈A) (b : Vertex → ℝ) :
    Measure.map (coordinates A V hVA).symm
      (BoundedData.law (BoundedData.activeGraph (finiteGraph A) (fixed A V)) (fixed A V) (fun x : A => b x.val))=law V b := by
  rw [← map_law A V hVA hcollar b,Measure.map_map (coordinates A V hVA).symm.measurable (coordinates A V hVA).measurable]
  simp only [Function.comp_def,MeasurableEquiv.symm_apply_apply]
  change Measure.map id (law V b)=law V b
  exact Measure.map_id

lemma one_sample_bounded_data (V : Finset Vertex) (b : Vertex → ℝ) (B : ℝ)
    (hB : 0≤B) (hb : ∀ x∉V,|b x|≤B) (hpos : 0<volume (body V b)) :
    ∃ π : Measure ((V → ℝ)×(V → ℝ)), IsProbabilityMeasure π ∧
    Measure.map Prod.fst π=law V b ∧ Measure.map Prod.snd π=SparseBlocks.law V ∧
    ∀ᵐ z∂π,∀ x : Vertex,|height V b z.1 x-SparseBlocks.height V z.2 x|≤B := by
  obtain ⟨A,hVA,hcollar,hc,hp⟩ := exists_ambient V
  let e := coordinates A V hVA
  let G := BoundedData.activeGraph (finiteGraph A) (fixed A V)
  have ha := BoundedData.activeGraph_anchored (finiteGraph A) hc (fixed A V) hp
  have hv : 0<volume (conditionalBody G (fixed A V) (fun x : A => b x.val)) := by
    rw [← (preserving_coordinates A V hVA).measure_preimage (closed_conditionalBody G _ _).measurableSet.nullMeasurableSet,
      body_coordinates A V hVA hcollar b]
    exact hpos
  obtain ⟨π,hπ,hfst,hsnd,hbound⟩ := AnchoredBoundedData.one_sample_bounded_data_anchored G (fixed A V) ha
    (fun x : A => b x.val) B hB (fun x hx => hb x.val hx) hv
  let := hπ
  let F : (Free (fixed A V) → ℝ)×(Free (fixed A V) → ℝ) → (V → ℝ)×(V → ℝ) := Prod.map e.symm e.symm
  have hF : MeasurableEmbedding F := e.symm.measurableEmbedding.prodMap e.symm.measurableEmbedding
  refine ⟨Measure.map F π,inferInstance,?_,?_,?_⟩
  · rw [Measure.map_map measurable_fst hF.measurable]
    change Measure.map (e.symm ∘ Prod.fst) π=law V b
    rw [← Measure.map_map e.symm.measurable measurable_fst,hfst]
    exact inverse_map_law A V hVA hcollar b
  · rw [Measure.map_map measurable_snd hF.measurable]
    change Measure.map (e.symm ∘ Prod.snd) π=SparseBlocks.law V
    rw [← Measure.map_map e.symm.measurable measurable_snd,hsnd]
    rw [inverse_map_law A V hVA hcollar (fun _ => 0),law_zero]
  · apply hF.ae_map_iff.mpr
    filter_upwards [hbound] with z hz
    intro x
    by_cases hx : x∈V
    · have h₁ := coordinates_height A V hVA b (e.symm z.1) ⟨x,hVA hx⟩
      have h₂ := coordinates_height A V hVA (fun _ => 0) (e.symm z.2) ⟨x,hVA hx⟩
      change restore (fixed A V) (fun x : A => b x.val) (e (e.symm z.1)) ⟨x,hVA hx⟩=height V b (e.symm z.1) x at h₁
      change restore (fixed A V) (fun _ : A => 0) (e (e.symm z.2)) ⟨x,hVA hx⟩=SparseBlocks.height V (e.symm z.2) x at h₂
      rw [e.apply_symm_apply] at h₁ h₂
      change |height V b (e.symm z.1) x-SparseBlocks.height V (e.symm z.2) x|≤B
      rw [← h₁,← h₂]
      exact hz ⟨x,hVA hx⟩
    · simpa [F,Prod.map,height,SparseBlocks.height,hx] using hb x hx

end BoundedLattice

namespace BoundedLattice

open Set MeasureTheory SparseBlocks MacroscopicAverages

open scoped NNReal

attribute [local instance] Classical.propDecidable

lemma continuous_statistic (V : Finset Vertex) (b : Vertex → ℝ) (q : Vertex →₀ ℝ) :
    Continuous (statistic V b q) := by
  exact continuous_finsetSum _ (fun x _ => continuous_const.mul (continuous_height V b x))

lemma statistic_difference_bound (V : Finset Vertex) (b : Vertex → ℝ) (q : Vertex →₀ ℝ)
    (h k : V → ℝ) (B C : ℝ) (hB : 0≤B) (hq : q.sum (fun _ t => |t|)≤C)
    (hb : ∀ x,|height V b h x-SparseBlocks.height V k x|≤B) :
    |statistic V b q h-MacroscopicAverages.statistic V q k|≤B*C := by
  have he : statistic V b q h-MacroscopicAverages.statistic V q k=
      ∑ x∈q.support,q x*(height V b h x-SparseBlocks.height V k x) := by
    simp only [statistic,MacroscopicAverages.statistic,Finsupp.sum,mul_sub,Finset.sum_sub_distrib]
  rw [he]
  calc
    |∑ x∈q.support,q x*(height V b h x-SparseBlocks.height V k x)| ≤
      ∑ x∈q.support,|q x*(height V b h x-SparseBlocks.height V k x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x∈q.support,|q x| * B := Finset.sum_le_sum (fun x hx => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _))
    _ = B*(q.sum (fun _ t => |t|)) := by rw [← Finset.sum_mul]; exact mul_comm _ _
    _ ≤ B*C := mul_le_mul_of_nonneg_left hq hB

lemma bounded_moment_transfer (V : Finset Vertex) (b : Vertex → ℝ) (q : Vertex →₀ ℝ)
    (B C a : ℝ) (hB : 0≤B) (ha : 0≤a) (hb : ∀ x∉V,|b x|≤B)
    (hpos : 0<volume (body V b)) (hq : q.sum (fun _ t => |t|)≤C) :
    (∫⁻ h,ENNReal.ofReal (Real.exp (a*|statistic V b q h|)) ∂law V b) ≤
      ENNReal.ofReal (Real.exp (a*(B*C))) *
      (∫⁻ h,ENNReal.ofReal (Real.exp (a*|MacroscopicAverages.statistic V q h|)) ∂SparseBlocks.law V) := by
  obtain ⟨π,hπ,hfst,hsnd,hbound⟩ := one_sample_bounded_data V b B hB hb hpos
  have hm : Measurable (fun h : V → ℝ => ENNReal.ofReal (Real.exp (a*|statistic V b q h|))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul (continuous_statistic V b q).abs)).measurable
  have hzero : Measurable (fun h : V → ℝ => ENNReal.ofReal (Real.exp (a*|MacroscopicAverages.statistic V q h|))) := by
    simpa only [statistic_zero,Function.comp_def,Pi.mul_apply] using
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul (continuous_statistic V (fun _ => 0) q).abs)).measurable)
  rw [← hfst,lintegral_map hm measurable_fst]
  have hle : (fun z : (V → ℝ)×(V → ℝ) => ENNReal.ofReal (Real.exp (a*|statistic V b q z.1|))) ≤ᵐ[π]
      (fun z => ENNReal.ofReal (Real.exp (a*(B*C))) * ENNReal.ofReal (Real.exp (a*|MacroscopicAverages.statistic V q z.2|))) := by
    filter_upwards [hbound] with z hz
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hd := statistic_difference_bound V b q z.1 z.2 B C hB hq hz
    have ht : |statistic V b q z.1|≤|MacroscopicAverages.statistic V q z.2|+B*C := by
      calc
        |statistic V b q z.1|=|statistic V b q z.1-MacroscopicAverages.statistic V q z.2+MacroscopicAverages.statistic V q z.2| := by rw [sub_add_cancel]
        _ ≤ |statistic V b q z.1-MacroscopicAverages.statistic V q z.2|+|MacroscopicAverages.statistic V q z.2| := abs_add_le _ _
        _ ≤ _ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left ht ha]
  refine (lintegral_mono_ae hle).trans_eq ?_
  have hzs : Measurable (fun z : (V → ℝ)×(V → ℝ) => ENNReal.ofReal (Real.exp (a*|MacroscopicAverages.statistic V q z.2|))) := hzero.comp measurable_snd
  rw [lintegral_const_mul _ hzs,← lintegral_map hzero measurable_snd,hsnd]

theorem bounded_pinned_exponential_moments (c C B : ℝ) (hc : 0<c) (hC : 0<C) (hB : 0≤B) :
    ∃ a : ℝ,0<a ∧ ∃ M : ℝ≥0,∀ (V : Finset Vertex) (b : Vertex → ℝ),
    (∀ x∉V,|b x|≤B) → 0<volume (body V b) →
    ∀ (R : ℝ),1≤R → ∀ (lo hi : Vertex) (q : Vertex →₀ ℝ),
    q.support ⊆ coordinateBox lo hi →
    (∀ x∈coordinateBox lo hi,∀ y∈coordinateBox lo hi,latticeDist x y≤C*R) →
    q.sum (fun _ t => |t|)≤C → (∀ x,|q x|≤C*R^(-2:ℤ)) →
    ((q.sum (fun _ t => t))=0 ∨ ∃ P : Finset Vertex,
      P⊆coordinateBox lo hi ∧ Disjoint P V ∧
      (TriangularLipschitz.latticeGraph.induce (P:Set Vertex)).Connected ∧
      ∃ x∈P,∃ y∈P,c*R≤latticeDist x y) →
    (∫⁻ h,ENNReal.ofReal (Real.exp (a*|statistic V b q h|)) ∂law V b)≤M := by
  obtain ⟨a,ha,M,hM⟩ := zero_pinned_exponential_moments c C hc hC
  refine ⟨a,ha,Real.toNNReal (Real.exp (a*(B*C)))*M,?_⟩
  intro V b hb hpos R hR lo hi q hqs hdiam hqsum hqmax hanchor
  calc
    (∫⁻ h,ENNReal.ofReal (Real.exp (a*|statistic V b q h|)) ∂law V b) ≤
      ENNReal.ofReal (Real.exp (a*(B*C))) *
      (∫⁻ h,ENNReal.ofReal (Real.exp (a*|MacroscopicAverages.statistic V q h|)) ∂SparseBlocks.law V) :=
        bounded_moment_transfer V b q B C a hB ha.le hb hpos hqsum
    _ ≤ ENNReal.ofReal (Real.exp (a*(B*C)))*(M:ENNReal) :=
      mul_le_mul_right (hM V R hR lo hi q hqs hdiam hqsum hqmax hanchor) _
    _ = _ := by rw [ENNReal.coe_mul]; rfl

end BoundedLattice

namespace BoundedLattice

open Set MeasureTheory SparseBlocks

def finiteDomainBody (D V : Finset Vertex) (b : Vertex → ℝ) : Set (V → ℝ) :=
  {h | ∀ x∈D,∀ y∈D,Adj x y → |height V b h x-height V b h y|≤1}

noncomputable def finiteDomainLaw (D V : Finset Vertex) (b : Vertex → ℝ) : Measure (V → ℝ) :=
  (volume (finiteDomainBody D V b))⁻¹ • volume.restrict (finiteDomainBody D V b)

end BoundedLattice

namespace BoundedLattice

open Set MeasureTheory SparseBlocks MacroscopicAverages

open scoped NNReal

lemma finiteDomainBody_eq (D V : Finset Vertex) (hVD : V⊆D)
    (hcollar : ∀ x∈V,∀ y,Adj x y → y∈D) (b : Vertex → ℝ)
    (hpos : 0<volume (finiteDomainBody D V b)) : finiteDomainBody D V b=body V b := by
  have hn : (finiteDomainBody D V b).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn,measure_empty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨h₀,hh₀⟩ := hn
  ext h
  constructor
  · intro hh x hx y hxy
    exact hh x (hVD hx) y (hcollar x hx y hxy) hxy
  · intro hh x hx y hy hxy
    by_cases hxV : x∈V
    · exact hh x hxV y hxy
    · by_cases hyV : y∈V
      · simpa only [abs_sub_comm] using hh y hyV x (adj_symm hxy)
      · have hfixed := hh₀ x hx y hy hxy
        simpa only [height,dite_eq_right hxV,dite_eq_right hyV] using hfixed

lemma finiteDomainLaw_eq (D V : Finset Vertex) (hVD : V⊆D)
    (hcollar : ∀ x∈V,∀ y,Adj x y → y∈D) (b : Vertex → ℝ)
    (hpos : 0<volume (finiteDomainBody D V b)) : finiteDomainLaw D V b=law V b := by
  simp only [finiteDomainLaw,law,finiteDomainBody_eq D V hVD hcollar b hpos]

theorem macroscopic_exponential_moments (c C B : ℝ) (hc : 0<c) (hC : 0<C) :
    ∃ a : ℝ,0<a ∧ ∃ M : ℝ≥0,∀ (D V : Finset Vertex), V⊆D → (∀ x∈V,∀ y,Adj x y → y∈D) →
    ∀ (b : Vertex → ℝ), (∀ x∉V,|b x|≤B) → 0<volume (finiteDomainBody D V b) →
    ∀ (R : ℝ),1≤R → ∀ (lo hi : Vertex) (q : Vertex →₀ ℝ),
    q.support ⊆ coordinateBox lo hi →
    (∀ x∈coordinateBox lo hi,∀ y∈coordinateBox lo hi,latticeDist x y≤C*R) →
    q.sum (fun _ t => |t|)≤C → (∀ x,|q x|≤C*R^(-2:ℤ)) →
    ((q.sum (fun _ t => t))=0 ∨ ∃ P : Finset Vertex,
      P⊆coordinateBox lo hi ∧ Disjoint P V ∧
      (TriangularLipschitz.latticeGraph.induce (P:Set Vertex)).Connected ∧
      ∃ x∈P,∃ y∈P,c*R≤latticeDist x y) →
    (∫⁻ h,ENNReal.ofReal (Real.exp (a*|statistic V b q h|)) ∂finiteDomainLaw D V b)≤M := by
  obtain ⟨a,ha,M,hM⟩ := bounded_pinned_exponential_moments c C (max B 0) hc hC (le_max_right B 0)
  refine ⟨a,ha,M,?_⟩
  intro D V hVD hcollar b hb hpos R hR lo hi q hqs hdiam hqsum hqmax hanchor
  rw [finiteDomainLaw_eq D V hVD hcollar b hpos]
  have hpos' : 0<volume (body V b) := by rwa [finiteDomainBody_eq D V hVD hcollar b hpos] at hpos
  exact hM V b (fun x hx => (hb x hx).trans (le_max_left B 0)) hpos' R hR lo hi q hqs hdiam hqsum hqmax hanchor

end BoundedLattice

namespace BoundedLattice

open Set MeasureTheory SparseBlocks MacroscopicAverages ProbabilityTheory

open scoped NNReal

attribute [local instance] Classical.propDecidable

lemma measurable_mixed_statistic {Ω : Type*} [MeasurableSpace Ω] (V : Finset Vertex)
    (b : Ω → Vertex → ℝ) (hb : ∀ x,Measurable (fun ω => b ω x)) (q : Vertex →₀ ℝ) :
    Measurable (fun z : Ω×(V → ℝ) => statistic V (b z.1) q z.2) := by
  apply Finset.measurable_sum
  intro x hx
  apply measurable_const.mul
  by_cases hxV : x∈V
  · simpa only [height,dite_eq_left hxV,Function.comp_def] using ((measurable_pi_apply (⟨x,hxV⟩ : V)).comp measurable_snd)
  · simpa only [height,dite_eq_right hxV,Function.comp_def] using ((hb x).comp measurable_fst)

theorem macroscopic_exponential_moments_mixtures (c C B : ℝ) (hc : 0<c) (hC : 0<C) :
    ∃ a : ℝ,0<a ∧ ∃ M : ℝ≥0,∀ (D V : Finset Vertex), V⊆D →
    (∀ x∈V,∀ y,Adj x y → y∈D) → ∀ (R : ℝ),1≤R → ∀ (lo hi : Vertex) (q : Vertex →₀ ℝ),
    q.support ⊆ coordinateBox lo hi →
    (∀ x∈coordinateBox lo hi,∀ y∈coordinateBox lo hi,latticeDist x y≤C*R) →
    q.sum (fun _ t => |t|)≤C → (∀ x,|q x|≤C*R^(-2:ℤ)) →
    ((q.sum (fun _ t => t))=0 ∨ ∃ P : Finset Vertex,
      P⊆coordinateBox lo hi ∧ Disjoint P V ∧
      (TriangularLipschitz.latticeGraph.induce (P:Set Vertex)).Connected ∧
      ∃ x∈P,∃ y∈P,c*R≤latticeDist x y) →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (b : Ω → Vertex → ℝ) (κ : Kernel Ω (V → ℝ)) [IsMarkovKernel κ],
    (∀ x,Measurable (fun ω => b ω x)) →
    (∀ᵐ ω∂ν,(∀ x∉V,|b ω x|≤B) ∧ 0<volume (finiteDomainBody D V (b ω)) ∧
      κ ω=finiteDomainLaw D V (b ω)) →
    (∫⁻ z,ENNReal.ofReal (Real.exp (a*|statistic V (b z.1) q z.2|)) ∂(ν ⊗ₘ κ))≤M := by
  obtain ⟨a,ha,M,hM⟩ := macroscopic_exponential_moments c C B hc hC
  refine ⟨a,ha,M,?_⟩
  intro D V hVD hcollar R hR lo hi q hqs hdiam hqsum hqmax hanchor Ω mΩ ν hν b κ hκ hb hcond
  have hf : Measurable (fun z : Ω×(V → ℝ) => ENNReal.ofReal (Real.exp (a*|statistic V (b z.1) q z.2|))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul (measurable_mixed_statistic V b hb q).abs))
  rw [Measure.lintegral_compProd hf]
  calc
    (∫⁻ ω,∫⁻ h,ENNReal.ofReal (Real.exp (a*|statistic V (b ω) q h|)) ∂κ ω ∂ν) ≤ ∫⁻ _ω,M ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hcond] with ω hω
      rw [hω.2.2]
      exact hM D V hVD hcollar (b ω) hω.1 hω.2.1 R hR lo hi q hqs hdiam hqsum hqmax hanchor
    _ = _ := by simp

end BoundedLattice

end

end OAI
