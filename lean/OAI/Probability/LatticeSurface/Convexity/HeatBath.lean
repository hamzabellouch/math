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

namespace BoundedData

open MeasureTheory ExtremalEdges Set

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

lemma compact_body (G : SimpleGraph V) (hc : G.Connected) (pins : Set V) (hp : pins.Nonempty)
    (b : V → ℝ) : IsCompact (conditionalBody G pins b) := by
  classical
  obtain ⟨p,hp⟩ := hp
  let path (x : V) : G.Walk x p := Classical.choice (hc x p)
  let R (x : Free pins) : ℝ := |b p|+(path x).length
  apply isCompact_Icc.of_isClosed_subset (closed_conditionalBody G pins b) (s := Icc (-R) R)
  intro h hh
  have hb (x : Free pins) : |h x|≤R x := by
    have hbnd := bound_along_walk G (restore pins b h) hh (path x)
    have hx : restore pins b h x=h x := by simp [restore,x.property]
    have hp' : restore pins b h p=b p := by simp [restore,hp]
    rw [hx,hp'] at hbnd
    have ht : |h x|≤|h x-b p|+|b p| := by simpa only [sub_add_cancel] using abs_add_le (h x-b p) (b p)
    dsimp [R]
    linarith
  exact ⟨fun x => (abs_le.mp (hb x)).1,fun x => (abs_le.mp (hb x)).2⟩

lemma neighbor_nonempty (G : SimpleGraph V) (hc : G.Connected) (pins : Set V) (hp : pins.Nonempty)
    (x : Free pins) : (G.neighborFinset x).Nonempty := by
  classical
  obtain ⟨p,hp⟩ := hp
  have hxp : (x:V)≠p := fun h => x.property (h ▸ hp)
  obtain ⟨w⟩ := hc x p
  cases w with
  | nil => exact (hxp rfl).elim
  | cons hxy w => exact ⟨_,by simpa using hxy⟩

noncomputable def lower (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (h : Free pins → ℝ) (x : Free pins) : ℝ :=
  (G.neighborFinset x).sup' (hn x) (fun y => restore pins b h y-1)

noncomputable def upper (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (h : Free pins → ℝ) (x : Free pins) : ℝ :=
  (G.neighborFinset x).inf' (hn x) (fun y => restore pins b h y+1)

lemma continuous_lower (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty) (b : V → ℝ) (x : Free pins) :
    Continuous (fun h => lower G pins hn b h x) := by
  unfold lower
  exact Continuous.finset_sup'_apply _ (fun y hy => (continuous_restore pins b y).sub continuous_const)

lemma continuous_upper (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty) (b : V → ℝ) (x : Free pins) :
    Continuous (fun h => upper G pins hn b h x) := by
  unfold upper
  exact Continuous.finset_inf'_apply _ (fun y hy => (continuous_restore pins b y).add continuous_const)

lemma lower_le (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty) (b : V → ℝ)
    (h : Free pins → ℝ) (hh : h∈conditionalBody G pins b) (x : Free pins) : lower G pins hn b h x≤h x := by
  apply Finset.sup'_le
  intro y hy
  have hb := (abs_le.mp (hh y x (by simpa [SimpleGraph.adj_comm] using hy))).2
  simpa [restore,x.property] using (show restore pins b h y-1≤restore pins b h x by linarith)

lemma le_upper (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty) (b : V → ℝ)
    (h : Free pins → ℝ) (hh : h∈conditionalBody G pins b) (x : Free pins) : h x≤upper G pins hn b h x := by
  apply Finset.le_inf'
  intro y hy
  have hb := (abs_le.mp (hh x y (by simpa using hy))).2
  simpa [restore,x.property] using (show restore pins b h x≤restore pins b h y+1 by linarith)

omit [Fintype V] in
lemma restore_update (pins : Set V) (b : V → ℝ) (h : Free pins → ℝ) (x : Free pins) (t : ℝ) (y : V) :
    restore pins b (Function.update h x t) y=if y=x then t else restore pins b h y := by
  classical
  by_cases hy : y=(x:V)
  · subst y
    simp [restore,x.property]
  · by_cases hp : y∈pins
    · simp [restore,hp,hy]
    · have hne : (⟨y,hp⟩:Free pins)≠x := fun he => hy (congrArg Subtype.val he)
      simp [restore,hp,hy,Function.update_of_ne hne]

lemma update_body (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty) (b : V → ℝ)
    (h : Free pins → ℝ) (hh : h∈conditionalBody G pins b) (x : Free pins) (t : ℝ)
    (ht : lower G pins hn b h x≤t ∧ t≤upper G pins hn b h x) :
    Function.update h x t∈conditionalBody G pins b := by
  classical
  have ha (y : V) (hy : G.Adj x y) : |t-restore pins b h y|≤1 := by
    have hl := (Finset.le_sup' (s := G.neighborFinset x) (f := fun y => restore pins b h y-1) (by simpa using hy)).trans ht.1
    have hu := ht.2.trans (Finset.inf'_le (s := G.neighborFinset x) (f := fun y => restore pins b h y+1) (by simpa using hy))
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro y z hyz
  rw [restore_update,restore_update]
  by_cases hy : y=(x:V)
  · subst y
    have hz : z≠(x:V) := hyz.ne.symm
    simpa [hz] using ha z hyz
  · by_cases hz : z=(x:V)
    · subst z
      simpa [hy,abs_sub_comm] using ha y hyz.symm
    · simpa [hy,hz] using hh y z hyz

noncomputable def update (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty) (b : V → ℝ)
    (x : Free pins) (h : Free pins → ℝ) (t : ℝ) : Free pins → ℝ :=
  Function.update h x ((1-t)*lower G pins hn b h x+t*upper G pins hn b h x)

lemma update_mem (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty) (b : V → ℝ)
    (x : Free pins) (h : Free pins → ℝ) (hh : h∈conditionalBody G pins b)
    {t : ℝ} (ht : t∈Icc 0 1) : update G pins hn b x h t∈conditionalBody G pins b := by
  apply update_body G pins hn b h hh x
  have hl := lower_le G pins hn b h hh x
  have hu := le_upper G pins hn b h hh x
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr (hl.trans hu)),mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hl.trans hu))]

lemma ascending_comparison (G : SimpleGraph V) (pins : Set V) (f g : V → ℝ)
    {bound : ℝ} (hpin : ∀ x∈pins,f x-g x≤bound) (hg : ∀ x y,G.Adj x y → |g x-g y|≤1)
    (hasc : ∀ x∉pins,∃ y,G.Adj x y ∧ f y=f x+1) : ∀ x,f x-g x≤bound := by
  classical
  intro x
  by_contra hx
  let S := Finset.univ.filter (fun x => bound<f x-g x)
  have hxS : x∈S := by simp [S];exact lt_of_not_ge hx
  obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image S f ⟨x,hxS⟩
  have hz' : bound<f z-g z := (Finset.mem_filter.mp hz).2
  have hzpin : z∉pins := fun hp => (not_lt_of_ge (hpin z hp)) hz'
  obtain ⟨y,hzy,hy⟩ := hasc z hzpin
  have hg' := (abs_le.mp (hg y z hzy.symm)).2
  have hyS : y∈S := by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and];linarith
  have := hmax y hyS
  linarith

lemma lower_fixed_comparison (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty) (b : V → ℝ) (B : ℝ)
    (hb : ∀ x∈pins,|b x|≤B) (h k : Free pins → ℝ)
    (hh : h∈conditionalBody G pins b) (hk : k∈conditionalBody G pins (fun _ => 0))
    (hf : ∀ x,lower G pins hn b h x=h x) (hg : ∀ x,lower G pins hn (fun _ => 0) k x=k x) :
    ∀ x,|restore pins b h x-restore pins (fun _ => 0) k x|≤B := by
  have asc (b : V → ℝ) (h : Free pins → ℝ) (he : ∀ x,lower G pins hn b h x=h x)
      (x : V) (hx : x∉pins) : ∃ y,G.Adj x y ∧ restore pins b h y=restore pins b h x+1 := by
    obtain ⟨y,hy,hval⟩ := Finset.exists_mem_eq_sup' (hn ⟨x,hx⟩) (fun y => restore pins b h y-1)
    refine ⟨y,by simpa using hy,?_⟩
    have hf' := he ⟨x,hx⟩
    change (G.neighborFinset x).sup' _ _=h ⟨x,hx⟩ at hf'
    rw [hval] at hf'
    have hxv : restore pins b h x=h ⟨x,hx⟩ := by simp [restore,hx]
    rw [hxv]
    linarith
  have hupper := ascending_comparison G pins (restore pins b h) (restore pins (fun _ => 0) k)
    (fun x hx => by simpa [restore,hx] using (abs_le.mp (hb x hx)).2) hk (asc b h hf)
  have hlower := ascending_comparison G pins (restore pins (fun _ => 0) k) (restore pins b h)
    (fun x hx => by simpa [restore,hx] using (show -b x≤B by linarith [(abs_le.mp (hb x hx)).1])) hh (asc _ k hg)
  intro x
  exact abs_le.mpr ⟨by linarith [hlower x],hupper x⟩

end BoundedData

end OAI
