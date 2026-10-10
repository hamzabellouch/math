import OAI.Geometry.SurfaceImmersion.Primitive.CurvedAtlasPrimitives
import OAI.Geometry.SurfaceImmersion.Primitive.PhasePrimitiveTensor
import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts

namespace OAI

/-! The first phase coordinate has the exact covector used by the local
rank-one tensor pullback. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates

namespace JetPolynomial
lemma firstPhaseCovector_apply (T : Base → Base) (x v : Base) :
    phaseLinear (firstPhaseCovector T x) (baseEquiv v) = (fderiv ℝ T x v) 0 := by
  have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 := by
    ext k
    fin_cases k <;> simp [coordinateVector]
  conv_rhs => rw [hv]
  simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  change (fderiv ℝ T x (coordinateVector 0)) 0 * v 0 +
    (fderiv ℝ T x (coordinateVector 1)) 0 * v 1 = _
  ring
end JetPolynomial

namespace FiniteOrderSmoothing.SmoothingAtlas
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable (A : SmoothingAtlas M)

lemma jetChart_tangentCoordinates (i : A.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base) (chart (i : M)) p =
      (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap.comp
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p) := by
  have hp' : p ∈ (chartAt Plane (i : M)).source := by simpa only [chart_source] using hp
  have hc := (contMDiffOn_chart (I := planeModel) (n := ∞) (x := (i : M)) p hp').contMDiffAt
    ((chartAt Plane (i : M)).open_source.mem_nhds hp')
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hp']
  change mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base)
    ((EuclideanSpace.equiv (Fin 2) ℝ) ∘ chartAt Plane (i : M)) p = _
  rw [mfderiv_comp p
    (((EuclideanSpace.equiv (Fin 2) ℝ).contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv,
    (EuclideanSpace.equiv (Fin 2) ℝ).fderiv]
  rfl

lemma phaseFirst_mfderiv (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) {phi : M → ℝ} {p : M}
    (hp : p ∈ (chart (i : M)).source)
    (hphi : phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0))
    (v : TangentSpace planeModel p) :
    mfderiv planeModel 𝓘(ℝ) phi p v =
      phaseLinear (JetPolynomial.firstPhaseCovector e (chart (i : M) p))
        (planeCoordinates
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)) := by
  let f : JetPolynomial.Base → ℝ := fun y => e y 0
  have hf : ContDiff ℝ ∞ f := (contDiff_pi.mp he 0)
  have hc := (chart_smooth (i : M) p hp).contMDiffAt ((chart (i : M)).open_source.mem_nhds hp)
  rw [hphi.mfderiv_eq]
  change mfderiv planeModel 𝓘(ℝ) (f ∘ chart (i : M)) p v = _
  rw [mfderiv_comp p (hf.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv,A.jetChart_tangentCoordinates i hp]
  change fderiv ℝ f (chart (i : M) p)
    ((EuclideanSpace.equiv (Fin 2) ℝ)
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)) = _
  rw [fderiv_apply (he.differentiable (by simp) _) 0]
  exact (JetPolynomial.firstPhaseCovector_apply e _ _).symm

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI
