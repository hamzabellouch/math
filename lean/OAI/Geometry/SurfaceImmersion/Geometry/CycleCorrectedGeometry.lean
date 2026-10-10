import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceCorrectedFamily
import OAI.Geometry.SurfaceImmersion.Primitive.CircularCycleMetrics
import OAI.Geometry.SurfaceImmersion.Geometry.IndependentRadiusBox
import OAI.Geometry.SurfaceImmersion.Primitive.PreparedCircularFamilyGeometry

namespace OAI

/-! Reference charts give the generic finite geometry for any number of
cycles without shrinking the admissible chart radii after that number is
chosen. The actual corrected families are then attached to those circles. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance cycleGeometryFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleGeometryFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleGeometryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance cycleGeometryDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance cycleGeometrySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleGeometrySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

/-- Use the already selected full-disk reference charts, for arbitrarily many
copies, rather than choosing a new admissible radius after the copy count. -/
theorem finite_copy_geometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι → d.B.centers) (component : ι → Fin 3)
    (lo hi : ι → ℝ) (hlo : ∀ a, 0 < lo a) (hlohi : ∀ a, lo a < hi a)
    (hhi : ∀ a, hi a < d.radius (index a))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ q : CircularFamilyGeometry d.B ι,
      (∀ a, lo a < q.radius a ∧ q.radius a < hi a) ∧
      (∀ a, (q.curves a).index = index a) ∧
      (∀ a, q.outerRadius a = d.radius (index a)) ∧
      (∀ a, q.chartRadius a = d.radius (index a)) ∧
      (∀ a, q.convexPart a = d.L (index a)) ∧
      (∀ a, ‖q.linearPart a-(d.P (index a)).ξ (component a)‖ < eta) ∧
      ∀ a, q.linearPart a ∈ Metric.closedBall ((d.P (index a)).ξ (component a))
        (d.epsilon (index a)) := by
  classical
  let eps : ι → ℝ := fun a => min eta (d.epsilon (index a))
  let U : Set (ι → Base) := {ell | ∀ a, ‖ell a-(d.P (index a)).ξ (component a)‖ < eps a}
  have hU : IsOpen U := by
    simp only [U,ofPred_forall]
    apply isOpen_iInter_of_finite
    intro a
    exact isOpen_lt (((continuous_apply a).sub continuous_const).norm) continuous_const
  have hne : U.Nonempty := by
    refine ⟨fun a => (d.P (index a)).ξ (component a),?_⟩
    intro a
    simpa only [sub_self,norm_zero] using lt_min heta (d.epsilon_pos (index a))
  obtain ⟨r,ell,hell,hr,hcross,htriple,htrans,htangent,hind⟩ :=
    d.B.finite_circular_preparation index (fun a => d.radius (index a)) lo hi
      (fun a => d.L (index a)) hlo hlohi hhi
      (fun a => d.weight_positive (index a)) (fun a => d.region (index a)) U hU hne
  have hball (a : ι) : ell a ∈ Metric.closedBall ((d.P (index a)).ξ (component a))
      (d.epsilon (index a)) := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    exact ((hell a).trans_le (min_le_right _ _)).le
  choose e he hei hephase hecover using fun a => d.charts (index a) (component a) (ell a) (hball a)
  have hrpos (a : ι) : 0 < r a := (hlo a).trans (hr a).1
  have hrr (a : ι) : r a < d.radius (index a) := (hr a).2.trans (hhi a)
  have hrreg (a : ι) : circularCoordinateRegion (index a : M) (r a) ⊆
      (coordinateChart (index a : M)).target := by
    intro x hx
    change circularRadiusSquared (coordinateChart (index a : M) (index a)) x ≤ (r a)^2 at hx
    exact d.region (index a) (hx.trans (by nlinarith [hrpos a,hrr a]))
  have hcover (a : ι) : ∀ x ∈ circularCoordinateRegion (index a : M) (r a),
      baseEquiv.symm x ∈ (e a).source := by
    intro x hx
    apply hecover a x
    change circularRadiusSquared (coordinateChart (index a : M) (index a)) x ≤ (r a)^2 at hx
    change circularRadiusSquared (coordinateChart (index a : M) (index a)) x ≤ (d.radius (index a))^2
    exact hx.trans (by nlinarith [hrpos a,hrr a])
  let curves : ι → PhaseBoundaryCurve d.B := fun a =>
    d.B.circularPhaseBoundaryCurve (index a) (hrpos a) (by nlinarith [hrpos a,hrr a])
      (d.weight_positive (index a)) (hrreg a) (e a) (he a) (hei a) (hcover a)
  have hcarrier (a : ι) : (curves a).carrier = circularBoundary (index a : M) (r a) := rfl
  have hsub : boundaryCrossingSet curves univ ⊆ circularCrossingSet (fun a => (index a : M)) r := by
    rintro p ⟨a,_,b,_,hab,hpa,hpb⟩
    exact mem_iUnion.mpr ⟨⟨(a,b),hab⟩,⟨hpa,hpb⟩⟩
  let q : CircularFamilyGeometry d.B ι := {
    curves := curves, radius := r, outerRadius := fun a => d.radius (index a),
    chartRadius := fun a => d.radius (index a), linearPart := ell, convexPart := fun a => d.L (index a),
    radius_pos := hrpos, radius_outer := fun a => by nlinarith [hrpos a,hrr a],
    radius_chart := hrr, weight_positive := fun a => d.weight_positive (index a),
    region := hrreg, carrier := hcarrier, cover := hcover, first_coordinate := hephase,
    pair_finite := fun a b hab => hcross.subset (fun _ hp => hsub
      (boundaryCrossingSet_pair curves (mem_univ a) (mem_univ b) hab hp.1 hp.2)),
    triple_empty := htriple, tangencies_finite := htangent,
    independent := fun a b hab p hp hpa hpb => hind a b hab p (hsub hp) hpa hpb }
  exact ⟨q,hr,(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),
    (fun a => (hell a).trans_le (min_le_left _ _)),hball⟩

end ReferenceCircularAtlas

namespace SmoothPrimitiveFamily
variable {u : ∀ p : M, CovariantTwoTensor p} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Reindex only the genuine finite family, preserving its exact sum. -/
def reindex (f : SmoothPrimitiveFamily ι u) (e : κ ≃ ι) : SmoothPrimitiveFamily κ u where
  amplitude := f.amplitude ∘ e
  phase := f.phase ∘ e
  smoothAmplitude a := f.smoothAmplitude (e a)
  smoothPhase a := f.smoothPhase (e a)
  sum_eq p := by
    simpa only [Function.comp_apply] using
      (e.sum_comp (fun a => (f.amplitude a p)^2 •
        SmoothingAtlas.phaseDifferentialSquare (f.phase a) p)).trans (f.sum_eq p)

end SmoothPrimitiveFamily

namespace CircularFamilyGeometry
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

/-- The actual restored phase, allowing repeated copies of a chart. -/
def copiedPhases (q : CircularFamilyGeometry B ι) (a : ι) : M → ℝ :=
  B.circularPhase (q.curves a).index (q.linearPart a) (q.convexPart a)

omit [CompactSpace M] [T2Space M] in
lemma copiedPhases_germ (q : CircularFamilyGeometry B ι)
    (houter : ∀ i p, p ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (a : ι) {p : M}
    (hp : p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a)) :
    q.copiedPhases a =ᶠ[𝓝 p]
      (fun x => ((q.curves a).phase (chart ((q.curves a).index : M) x)) 0) := by
  have hw : B.weight (q.curves a).index p ≠ 0 := by
    apply ne_of_gt ((q.weight_positive a p).mpr ?_)
    exact ⟨hp.1,hp.2.trans (q.radius_outer a)⟩
  let loc : B.centers → Fin 3 → Base → ℝ := fun i _ =>
    centeredConvexPhase (q.linearPart a) (q.convexPart a) (coordinateChart (i : M) i)
  have hg := B.curvedAtlasPhase_eventually loc ((q.curves a).index,0)
    (houter (q.curves a).index) (subset_tsupport _ hw)
  change q.copiedPhases a =ᶠ[𝓝 p]
    (centeredConvexPhase (q.linearPart a) (q.convexPart a)
      (coordinateChart ((q.curves a).index : M) (q.curves a).index) ∘
        coordinateChart ((q.curves a).index : M)) at hg
  apply hg.trans
  apply Filter.Eventually.of_forall
  intro x
  have hh := q.first_coordinate a (chart ((q.curves a).index : M) x)
  change ((q.curves a).phase (chart ((q.curves a).index : M) x)) 0 = _ at hh
  exact hh.symm

omit [CompactSpace M] [T2Space M] in
/-- Attach cycle amplitudes without changing any selected generic geometry. -/
theorem with_cycle_families {N m : ℕ} (q : CircularFamilyGeometry B (Fin (N*m)))
    {u : ∀ p : M, CovariantTwoTensor p}
    (f : Fin N → SmoothPrimitiveFamily (Fin m) u) (hN : 0 < N)
    (hamp : ∀ k a p, 0 ≤ (f k).amplitude a p)
    (hpos : ∀ a p, 0 < (f a.divNat).amplitude a.modNat p ↔
      p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a))
    (hphase : ∀ a, (f a.divNat).phase a.modNat = q.copiedPhases a)
    (houter : ∀ i p, p ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ D : CircularPrimitiveFamily B (Fin (N*m)),
      D.curves = q.curves ∧ D.radius = q.radius ∧ D.outerRadius = q.outerRadius ∧
      D.chartRadius = q.chartRadius ∧ D.linearPart = q.linearPart ∧ D.convexPart = q.convexPart ∧
      (∀ a p, D.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) ∧
      (∀ a, D.phase a = (f a.divNat).phase a.modNat) ∧ D.totalTensor = u := by
  let amp := fun a : Fin (N*m) => (f a.divNat).cycleAmplitude N a.modNat
  let phi := fun a : Fin (N*m) => (f a.divNat).phase a.modNat
  have ha : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (amp a) :=
    fun a => (f a.divNat).cycleAmplitude_smooth N a.modNat
  have hp : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a) :=
    fun a => (f a.divNat).smoothPhase a.modNat
  have hn : ∀ a p, 0 ≤ amp a p := fun a p =>
    div_nonneg (hamp _ _ _) (Real.sqrt_nonneg _)
  have hpos' : ∀ a p, 0 < amp a p ↔
      p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a) := by
    intro a p
    exact ((f a.divNat).cycleAmplitude_pos_iff hN a.modNat p).trans (hpos a p)
  have hg : ∀ a p, p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a) →
      phi a =ᶠ[𝓝 p] (fun x => ((q.curves a).phase (chart ((q.curves a).index : M) x)) 0) := by
    intro a p hpa
    change (f a.divNat).phase a.modNat =ᶠ[𝓝 p] _
    rw [hphase a]
    exact q.copiedPhases_germ houter a hpa
  let D := q.withAmplitudes amp phi ha hp hn hpos' hg
  refine ⟨D,rfl,rfl,rfl,rfl,rfl,rfl,(fun _ _ => rfl),(fun _ => rfl),?_⟩
  exact D.totalTensor_cycle f (fun _ _ => rfl) (fun _ => rfl) hN

end CircularFamilyGeometry

namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

def cycleLinearParts {N m : ℕ} (e : Fin m ≃ (d.B.centers × Fin 3))
    (q : CircularFamilyGeometry d.B (Fin (N*m))) (k : Fin N) (i : d.B.centers) (j : Fin 3) : Base :=
  q.linearPart (finProdFinEquiv (k,e.symm (i,j)))

def cycleWeights {N m : ℕ} (e : Fin m ≃ (d.B.centers × Fin 3))
    (q : CircularFamilyGeometry d.B (Fin (N*m))) (k : Fin N) (b : d.B.centers × Fin 3) : M → ℝ :=
  shrinkingCircularWeight (b.1 : M) (d.B.weight b.1) (d.radius b.1)
    (q.radius (finProdFinEquiv (k,e.symm b)))

/-- One radius box and map neighborhood precede every cycle count. The
output retains the actual amplitude formula and fixed cutoff bounds, so
the uniform C1 estimate can be applied without choosing further constants. -/
theorem corrected_cycles {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F))
    {phaseBound weightBound mapBound : ℝ}
    (hphaseBound : 0 < phaseBound) (hweightBound : 0 < weightBound)
    (hmapBound : 0 < mapBound)
    {m : ℕ} (e : Fin m ≃ (d.B.centers × Fin 3)) :
    ∃ (mapTol delta : ℝ) (W : ℕ → ℝ),
      0 < mapTol ∧ mapTol ≤ mapBound ∧ 0 < delta ∧
      (∀ i, delta ≤ d.radius i/2) ∧ (∀ j, 0 ≤ W j) ∧
      ∀ N : ℕ, 0 < N →
      ∃ q : CircularFamilyGeometry d.B (Fin (N*m)),
        (∀ a, (q.curves a).index = (e a.modNat).1) ∧
        (∀ a, q.outerRadius a = d.radius (e a.modNat).1) ∧
        (∀ a, q.chartRadius a = d.radius (e a.modNat).1) ∧
        (∀ a, q.convexPart a = d.L (e a.modNat).1) ∧
        (∀ a, ‖q.linearPart a‖ ≤ ‖(d.P (e a.modNat).1).ξ‖+1) ∧
        (∀ a, ‖q.linearPart a-(d.P (e a.modNat).1).ξ (e a.modNat).2‖ < phaseBound) ∧
        (∀ k b j, d.B.WeightedBound 1 j (W j) (d.cycleWeights e q k b)) ∧
        (∀ k b p, |d.cycleWeights e q k b p-d.B.weight b.1 p| < weightBound) ∧
        ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
          A.WeightedBound 1 1 mapTol (G-F) →
        ∃ (f : Fin N → SmoothPrimitiveFamily (Fin m) (g.inner-inducedTensor (r • G)))
          (D : CircularPrimitiveFamily d.B (Fin (N*m))),
          (∀ k a, (f k).amplitude a = d.B.correctedPrimitiveAmplitude d.basis
            (d.cycleWeights e q k) (d.perturbedPhases (d.cycleLinearParts e q k))
            (g.inner-inducedTensor (r • G)) (e a)) ∧
          (∀ k a, (f k).phase a = d.perturbedPhases (d.cycleLinearParts e q k) (e a)) ∧
          D.curves = q.curves ∧ D.radius = q.radius ∧ D.outerRadius = q.outerRadius ∧
          D.chartRadius = q.chartRadius ∧ D.linearPart = q.linearPart ∧ D.convexPart = q.convexPart ∧
          (∀ a p, D.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) ∧
          (∀ a, D.phase a = (f a.divNat).phase a.modNat) ∧
          D.totalTensor = g.inner-inducedTensor (r • G) := by
  classical
  obtain ⟨pt,wt,mt,hpt,hwt,hmt,hcorrect⟩ := d.corrected_smooth_family hF r href
  obtain ⟨delta,W,hdelta,hdeltaR,hW,hweights⟩ := d.B.independent_radius_box
    (fun b : d.B.centers × Fin 3 => b.1) (fun b => d.radius b.1)
    (fun b => d.weight_nonneg b.1) (fun b => d.radius_pos b.1) (fun b => d.region b.1)
    (fun b => d.weight_positive b.1) (lt_min hwt hweightBound)
  refine ⟨min mt mapBound,delta,W,lt_min hmt hmapBound,min_le_right _ _,hdelta,
    (fun i => hdeltaR (i,0)),hW,?_⟩
  intro N hN
  let ind := fun a : Fin (N*m) => (e a.modNat).1
  let cmp := fun a : Fin (N*m) => (e a.modNat).2
  let lo := fun a : Fin (N*m) => d.radius (ind a)-delta
  let hi := fun a : Fin (N*m) => d.radius (ind a)-delta/2
  have hlo (a : Fin (N*m)) : 0 < lo a := by
    have hh := hdeltaR (ind a,cmp a)
    have hp := d.radius_pos (ind a)
    dsimp only [lo]
    linarith
  have hmid (a : Fin (N*m)) : lo a < hi a := by dsimp only [lo,hi]; linarith
  have hhi (a : Fin (N*m)) : hi a < d.radius (ind a) := by dsimp only [hi]; linarith
  obtain ⟨q,hr,hindex,houter,hchart,hL,hell,hball⟩ :=
    d.finite_copy_geometry ind cmp lo hi hlo hmid hhi (lt_min hpt hphaseBound)
  let copy := fun (k : Fin N) (b : d.B.centers × Fin 3) => finProdFinEquiv (k,e.symm b)
  have hcopy (k : Fin N) (b : d.B.centers × Fin 3) :
      (copy k b).divNat = k ∧ e (copy k b).modNat = b := by
    have hh := Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k,e.symm b))
    exact ⟨hh.1,by rw [hh.2,e.apply_symm_apply]⟩
  have hcopy' (a : Fin (N*m)) : copy a.divNat (e a.modNat) = a := by
    simp only [copy,e.symm_apply_apply]
    exact finProdFinEquiv.apply_symm_apply a
  let rr := fun (k : Fin N) (b : d.B.centers × Fin 3) => q.radius (copy k b)
  let ell := d.cycleLinearParts e q
  let psi := d.cycleWeights e q
  have hrr (k : Fin N) (b : d.B.centers × Fin 3) :
      d.radius b.1-delta < rr k b ∧ rr k b < d.radius b.1-delta/2 := by
    have hh := hr (copy k b)
    simpa only [lo,hi,ind,(hcopy k b).2,rr] using hh
  have hpsi (k : Fin N) := hweights (rr k) (hrr k)
  have hrsmall (k : Fin N) (b : d.B.centers × Fin 3) : (rr k b)^2 < (d.radius b.1)^2 := by
    have hh := hrr k b
    have hp := (hpsi k).1 b
    have hR := d.radius_pos b.1
    nlinarith
  have hnorm (a : Fin (N*m)) : ‖q.linearPart a‖ ≤ ‖(d.P (ind a)).ξ‖+1 :=
    (d.parameters (ind a) (cmp a) (q.linearPart a) (hball a)).2
  refine ⟨q,hindex,houter,hchart,hL,hnorm,
    (fun a => (hell a).trans_le (min_le_right _ _)),
    (fun k => (hpsi k).2.2.2.2.2),
    (fun k b p => ((hpsi k).2.2.2.2.1 b p).trans_le (min_le_right _ _)),?_⟩
  intro G hG hGF
  have hnon (k : Fin N) (b : d.B.centers × Fin 3) (p : M) : 0 ≤ psi k b p :=
    (shrinkingCircularWeight_nonneg_le (b.1 : M) (d.B.weight b.1)
      (d.weight_nonneg b.1) (hrsmall k b).le p).1
  have hsupp (k : Fin N) (b : d.B.centers × Fin 3) :
      tsupport (psi k b) ⊆ tsupport (d.B.weight b.1) := by
    apply closure_mono
    intro p hp
    change psi k b p ≠ 0 at hp
    change d.B.weight b.1 p ≠ 0
    intro hz
    exact hp (by simp only [psi,cycleWeights,shrinkingCircularWeight,hz,zero_mul])
  have hell' (k : Fin N) (i : d.B.centers) (j : Fin 3) :
      ‖ell k i j-(d.P i).ξ j‖ < pt := by
    have hh := (hell (copy k (i,j))).trans_le (min_le_left _ _)
    simpa only [ind,cmp,(hcopy k (i,j)).2,ell,cycleLinearParts] using hh
  choose fc hphase hamp hnonamp hposamp hsamp using fun k : Fin N =>
    hcorrect (ell k) (psi k) (hell' k) (hpsi k).2.1 (hnon k) (hsupp k)
      (fun b p => ((hpsi k).2.2.2.2.1 b p).trans_le (min_le_left _ _)) G hG
      (fun i => (hGF i).mono_const (min_le_left _ _))
  let f := fun k => (fc k).reindex e
  have hphase' (a : Fin (N*m)) : (f a.divNat).phase a.modNat = q.copiedPhases a := by
    change (fc a.divNat).phase (e a.modNat) = _
    rw [hphase a.divNat]
    change d.B.circularPhase (e a.modNat).1
      (ell a.divNat (e a.modNat).1 (e a.modNat).2) (d.L (e a.modNat).1) = _
    rw [show ell a.divNat (e a.modNat).1 (e a.modNat).2 = q.linearPart a from by
      change q.linearPart (copy a.divNat (e a.modNat)) = q.linearPart a
      rw [hcopy' a]]
    simp only [CircularFamilyGeometry.copiedPhases,hindex a,hL a,ind]
  have hpositive (a : Fin (N*m)) (p : M) :
      0 < (f a.divNat).amplitude a.modNat p ↔
        p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a) := by
    change 0 < (fc a.divNat).amplitude (e a.modNat) p ↔ _
    rw [hposamp a.divNat (e a.modNat) p]
    have hh := (hpsi a.divNat).2.2.1 (e a.modNat) p
    change 0 < psi a.divNat (e a.modNat) p ↔ _ at hh
    simpa only [rr,hcopy' a,hindex a,ind] using hh
  obtain ⟨D,hD⟩ := q.with_cycle_families f hN
    (fun k a p => hnonamp k (e a) p) hpositive hphase' d.outer
  refine ⟨f,D,?_,?_,hD⟩
  · intro k a
    change (fc k).amplitude (e a) = _
    exact congrFun (hamp k) (e a)
  · intro k a
    change (fc k).phase (e a) = _
    exact congrFun (hphase k) (e a)

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
