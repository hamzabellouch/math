import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitivePatch
import OAI.Geometry.SurfaceImmersion.Primitive.IndependentCircularBoundaryStep
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitivePatchBoundary
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteBoundaryStepGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.PreparedPhaseCrossingSlopes

namespace OAI

/-! The constructed local primitive data feed the exact analytic theorem,
with the global rank-one metric written in the original surface variables. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
local instance patchStepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance patchStepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance patchStepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance patchStepDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance patchStepSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance patchStepSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SupportedPrimitivePatch
variable {A : SmoothingAtlas M} {i : A.centers}
    {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
    {F : M → Space} {amp phi : M → ℝ} {D : Set M}

theorem boundary_step {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]
    (d : SupportedPrimitivePatch A i e F amp phi D)
    (c₀ : PhaseBoundaryCurve B) (hi : (i : M) = (c₀.index : M))
    (he : ∀ x, e x = c₀.phase x)
    (curves : ι → PhaseBoundaryCurve B)
    (hpair : ∀ j k, j ≠ k → ((curves j).carrier ∩ (curves k).carrier).Finite)
    (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅)
    (hD : IsOpen D) (hDr : interior (closure D) = D) (hfront : c₀.carrier = frontier D)
    (hEf : Disjoint (boundaryCrossingSet curves univ) (frontier D))
    {g : SmoothMetric M} (data : MetricGoodPhaseData g F)
    (hF : IsSmoothIsometricImmersion M g F) (n : PreferredNormal F)
    (hgeom : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n)
    (hcurrent : ∀ p ∈ c₀.carrier, c₀.second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (c₀.second F p))
    (hfrontGeom : ∀ j p, p ∈ (curves j).carrier ∩ frontier D →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
      0 < c₀.crossing (curves j) F p)
    (hfirst : ∀ j p, p ∈ boundaryCrossingSet curves univ ∩ D → p ∈ (curves j).carrier →
      (fderiv ℝ (surfacePhaseTransition ((curves j).index : M) (curves j).phase
        (i : M) e) ((curves j).coordinate p) dy).1 ≠ 0)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, d.curve (curves j)) \ P,
      ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧ ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, d.curve (curves j)) ∩ N, f x = 0) ∧ fderiv ℝ f p dy ≠ 0)
    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W, FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) W N := by
  classical
  let E₀ := boundaryCrossingSet curves (univ : Set ι)
  have hE₀ : E₀.Finite := boundaryCrossingSet_finite curves univ hpair
  let σ := E₀ ∩ D
  let : Fintype σ := (hE₀.inter_of_left D).fintype
  obtain ⟨l,r,hlr,honly⟩ := boundaryCrossingSet_select curves univ htriple
  let left : σ → ι := fun p => l ⟨p,p.2.1⟩
  let right : σ → ι := fun p => r ⟨p,p.2.1⟩
  let x : σ → SmallModes.Base := fun p => surfacePhaseChart (i : M) e p
  choose b k hb hk hbk hv using fun j => d.curve_coefficients (curves j)
  have hsource (p : σ) : (p : M) ∈ (surfacePhaseChart (i : M) e).source :=
    d.source_closed (subset_closure p.2.2)
  have hxback (p : σ) : (surfacePhaseChart (i : M) e).symm (x p) = p :=
    (surfacePhaseChart (i : M) e).left_inv (hsource p)
  have hxinj : Function.Injective x := by
    intro p q hpq
    apply Subtype.ext
    have hh := congrArg (surfacePhaseChart (i : M) e).symm hpq
    simpa only [hxback] using hh
  have hxE (p : σ) : x p ∈ d.innerCrossings E₀ := ⟨p,p.2,rfl⟩
  have hxl (p : σ) : (p : M) ∈ (curves (left p)).carrier := (hlr ⟨p,p.2.1⟩).2.2.2.1
  have hxr (p : σ) : (p : M) ∈ (curves (right p)).carrier := (hlr ⟨p,p.2.1⟩).2.2.2.2
  have hfirst' (p : σ) : b (left p) (x p) ≠ 0 ∧ b (right p) (x p) ≠ 0 := by
    have hf (j : ι) (hp : (p : M) ∈ (curves j).carrier) : b j (x p) ≠ 0 := by
      have hh := congrArg Prod.fst (hv j p ⟨hp,subset_closure p.2.2⟩)
      change b j (x p) = _ at hh
      rw [hh]
      exact hfirst j p p.2 hp
    exact ⟨hf _ (hxl p),hf _ (hxr p)⟩
  obtain ⟨L,hL,hslopes⟩ := finite_crossing_slope_bound
    (fun p : σ => (b (left p) (x p),k (left p) (x p)))
    (fun p : σ => (b (right p) (x p),k (right p) (x p)))
  have hmetric : g.inner = inducedTensor F := by
    funext p
    ext v w
    exact (hF.2 p v w).symm
  have htarget' : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e d.cutoff
        (fun q => ![(d.amplitude (baseEquiv q))^2,0,0]) y)) := by
    rw [d.tensor]
    exact htarget
  have hCS : d.compactSet ⊆ (d.window : Set JetPolynomial.Base) ∩ e.target :=
    fun _ hx => ⟨d.support_window hx,d.target hx⟩
  let ell : JetPolynomial.Base →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hell₀ : ell (coordinateVector 0) = 1 := by simp [ell,coordinateVector]
  have hell₁ : ell (coordinateVector 1) = 0 := by simp [ell,coordinateVector]
  have hworld : ∀ p ∈ frontier D,
      realSecondForm (A.phaseRealChartMap i e.symm F) dy dy (surfacePhaseChart (i : M) e p) ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize
        (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy (surfacePhaseChart (i : M) e p)) := by
    intro p hp
    have hpc : p ∈ c₀.carrier := hfront.symm ▸ hp
    rw [← d.current_second c₀ hi he hF hpc hp.1]
    exact hcurrent p hpc
  have honly' : ∀ p j, x p ∈ d.curve (curves j) → j = left p ∨ j = right p := by
    intro p j hp
    obtain ⟨q,hq,hqp⟩ := hp
    have heq : q = (p : M) := (surfacePhaseChart (i : M) e).injOn
      (d.source_closed hq.2) (hsource p) hqp
    subst q
    exact honly ⟨p,p.2.1⟩ j hq.1
  have hafront : ∀ p ∈ frontier D, d.amplitude (surfacePhaseChart (i : M) e p) = 0 := by
    intro p hp
    have hz : ¬ 0 < d.amplitude (surfacePhaseChart (i : M) e p) := by
      rw [d.amplitude_positive]
      rintro ⟨q,hq,heq⟩
      have hqp := (surfacePhaseChart (i : M) e).injOn
        (d.source_closed (subset_closure hq)) (d.source_closed hp.1) heq
      subst q
      exact hp.2 (hD.interior_eq.symm ▸ hq)
    exact le_antisymm (le_of_not_gt hz) (d.amplitude_nonneg _)
  have hvfront : ∀ p ∈ frontier D, surfacePhaseChart (i : M) e p ∉ (surfacePhaseChart (i : M) e) '' D := by
    intro p hp hpin
    obtain ⟨q,hq,heq⟩ := hpin
    have hqp := (surfacePhaseChart (i : M) e).injOn
      (d.source_closed (subset_closure hq)) (d.source_closed hp.1) heq
    subst q
    exact hp.2 (hD.interior_eq.symm ▸ hq)
  obtain ⟨W,hW,hgood,N,havoid,hcross⟩ :=
    data.independent_circular_primitive_boundary_step A d.outer hF.1 hmetric i e
      d.phase_smooth d.inverse_smooth d.cutoff_smooth d.cutoff_compact d.cutoff_source d.cover
      d.amplitude_smooth d.region_compact d.open_region d.region_open d.normal_smooth
      d.immersion d.normal_properties d.convexity d.amplitude_nonneg d.boundary
      (fun j => d.curve_compact (curves j)) (fun j => d.curve_region (curves j)) hP hlocal
      (d.innerCrossings_finite hE₀) (d.innerCrossings_region E₀) (d.innerCrossings_positive E₀)
      L hL hb hk hbk d.window d.window_compact d.phase_window d.window_region
      d.compactSet d.compact d.support_window d.inverse_support d.cutoff_one d.amplitude_off
      ell hell₀ hell₁ h htarget' d.compact hCS
      (fun j => d.curve_compact_coordinates (curves j)) d.compact_active
      (d.innerCrossings_compact_coordinates E₀)
      (fun j => d.old_boundary_crossing c₀ (curves j) hi he hD hfront hF (b j) (k j)
        (hv j) (fun p hp => (hfrontGeom j p hp).2))
      left right x hxinj hxE (V := (surfacePhaseChart (i : M) e) '' D)
      ((surfacePhaseChart (i : M) e).isOpen_image_of_subset_source hD
        (fun p hp => d.source_closed (subset_closure hp)))
      (fun p => ⟨p,p.2.2,rfl⟩) honly' hfirst' hslopes B curves n
      (fun j p hp => ⟨hgeom.nonzero j p hp,hgeom.avoids j p hp⟩)
      hD hDr (fun p hp => (d.source_closed hp).1) (fun p hp => (d.source_closed hp).2)
      d.active_closed E₀ hE₀ hEf d.support d.closed_coordinates
      (fun j p hp hpD => ⟨p,⟨hp,hpD⟩,rfl⟩)
      (fun j p hp hpD => hv j p ⟨hp,hpD⟩) hworld
      hafront (fun j p hp hpD => (hfrontGeom j p ⟨hp,hpD⟩).1) hvfront
      (fun p => by rw [hxback]; exact p.2)
      (fun p hp hpD => ⟨⟨p,hp,hpD⟩,hxback ⟨p,hp,hpD⟩⟩)
      (fun j k hjk p hp hj hk =>
        ⟨⟨hgeom.positive j k hjk p hp hj hk,hgeom.positive k j hjk.symm p hp hk hj⟩,
          hgeom.crossing j k hjk p hp hj hk,hgeom.crossing k j hjk.symm p hp hk hj⟩)
  exact ⟨W,hW,hgood,N,{
      nonzero := fun j p hp => (havoid j p hp).1
      avoids := fun j p hp => (havoid j p hp).2
      positive := fun j k hjk p hp hj hk => (hcross j k hjk p hp hj hk).1.1
      crossing := fun j k hjk p hp hj hk => (hcross j k hjk p hp hj hk).2.1 }⟩

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
