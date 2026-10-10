import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyGeometry
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPrimitiveFamily
import OAI.Geometry.SurfaceImmersion.Primitive.CurvedAtlasPrimitives

namespace OAI

/-! Actual corrected amplitudes and localized phases on the selected circles.
The remaining operator hypotheses are finite coefficient invertibility and positivity. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance correctedCircularFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance correctedCircularFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance correctedCircularDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance correctedCircularDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance correctedCircularSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance correctedCircularSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace CircularFamilyGeometry
variable {A : SmoothingAtlas M} (q : CircularFamilyGeometry A (A.centers × Fin 3))

def localPhases (i : A.centers) (j : Fin 3) : Base → ℝ :=
  centeredConvexPhase (q.linearPart (i,j)) (q.convexPart (i,j)) (coordinateChart (i : M) i)

def globalPhases : (A.centers × Fin 3) → M → ℝ := A.curvedAtlasPhase q.localPhases

omit [CompactSpace M] [T2Space M] in
lemma globalPhases_smooth (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (q.globalPhases a) :=
  A.curvedAtlasPhase_smooth q.localPhases (fun _ _ => centeredConvexPhase_smooth _ _ _) a

omit [CompactSpace M] [T2Space M] in
lemma globalPhases_germ
    (hindex : ∀ a, (q.curves a).index = a.1)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (a : A.centers × Fin 3) {p : M}
    (hp : p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a)) :
    q.globalPhases a =ᶠ[𝓝 p] (fun x => ((q.curves a).phase (chart ((q.curves a).index : M) x)) 0) := by
  have hw : A.weight a.1 p ≠ 0 := by
    rw [← hindex a]
    apply ne_of_gt ((q.weight_positive a p).mpr ?_)
    refine ⟨hp.1,?_⟩
    change circularRadiusSquared (coordinateChart ((q.curves a).index : M) (q.curves a).index)
      (coordinateChart ((q.curves a).index : M) p) < (q.outerRadius a)^2
    exact hp.2.trans (q.radius_outer a)
  have hg := A.curvedAtlasPhase_eventually q.localPhases a (houter a.1) (subset_tsupport _ hw)
  apply hg.trans
  apply Filter.Eventually.of_forall
  intro x
  have hh := q.first_coordinate a (chart ((q.curves a).index : M) x)
  change ((q.curves a).phase (chart ((q.curves a).index : M) x)) 0 = _ at hh
  rw [hindex a] at hh
  change q.localPhases a.1 a.2 (coordinateChart (a.1 : M) x) = _
  rw [hindex a]
  exact hh.symm

omit [T2Space M] in
 theorem corrected_family
    (hindex : ∀ a, (q.curves a).index = a.1)
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hpsi0 : ∀ a p, 0 ≤ psi a p)
    (hpsiPos : ∀ a p, 0 < psi a p ↔
      p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hinv : ∀ p, (A.primitiveFullOperator P psi q.globalPhases p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hsymm : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi q.globalPhases u p)) :
    ∃ d : CircularPrimitiveFamily A (A.centers × Fin 3),
      d.curves = q.curves ∧ d.radius = q.radius ∧ d.outerRadius = q.outerRadius ∧
      d.chartRadius = q.chartRadius ∧ d.linearPart = q.linearPart ∧ d.convexPart = q.convexPart ∧
      d.phase = q.globalPhases ∧ d.amplitude = A.correctedPrimitiveAmplitude P psi q.globalPhases u ∧
      ∀ p, (∑ a, (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p) = u p := by
  let amp := A.correctedPrimitiveAmplitude P psi q.globalPhases u
  have hamp : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (amp a) := fun a =>
    A.correctedPrimitiveAmplitude_smooth_of_data P psi q.globalPhases hpsi q.globalPhases_smooth
      hsupport hQ houter hinv u hu hpos a
  have hamp0 : ∀ a p, 0 ≤ amp a p := fun a p => mul_nonneg (hpsi0 a p) (Real.sqrt_nonneg _)
  have hpositive : ∀ a p, 0 < amp a p ↔
      p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a) := fun a p =>
    (A.correctedPrimitiveAmplitude_pos_iff P psi q.globalPhases u hpos a p).trans (hpsiPos a p)
  let d := q.withAmplitudes amp q.globalPhases hamp q.globalPhases_smooth hamp0 hpositive
    (fun a p hp => q.globalPhases_germ hindex houter a hp)
  refine ⟨d,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact A.correctedPrimitiveAmplitude_reconstruct P psi q.globalPhases hinv u hsymm
    (fun a p hp => (hpos a p hp).le)

end CircularFamilyGeometry
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
