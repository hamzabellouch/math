import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveFrameBounds
import OAI.Geometry.SurfaceImmersion.Primitive.CenteredAtlasPrimitives

namespace OAI

/-! Exact affine dependence of supported circular phases on their linear
parameters. The curvature parameter stays fixed. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def circularPhase (i : B.centers) (ell : Base) (L : ℝ) : M → ℝ :=
  restore (i : M) (B.outer i)
    (centeredConvexPhase ell L (coordinateChart (i : M) i) ∘ JetPolynomial.planeCoordinateIsometry)

omit [CompactSpace M] [T2Space M] in
lemma circularPhase_smooth (i : B.centers) (ell : Base) (L : ℝ) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (B.circularPhase i ell L) :=
  restore_smooth (i : M) (B.outer_smooth i) (B.outer_support i)
    ((centeredConvexPhase_smooth _ _ _).comp JetPolynomial.planeCoordinateIsometry.contDiff)

omit [CompactSpace M] [T2Space M] in
lemma circularPhase_sub (i : B.centers) (ell ell₀ : Base) (L : ℝ) :
    B.circularPhase i ell L-B.circularPhase i ell₀ L =
      (ell.1-ell₀.1) • B.circularPhase i (1,0) 0+
        (ell.2-ell₀.2) • B.circularPhase i (0,1) 0 := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [circularPhase,restore,hp,indicator_of_mem,Function.comp_apply,
      Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,centeredConvexPhase,
      convexQuadraticPhase,phaseLinear,Prod.fst_sub,Prod.snd_sub,
      add_apply,smul_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  · simp only [circularPhase,restore,indicator_of_notMem hp,Pi.sub_apply,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,sub_self,mul_zero,add_zero]

omit [CompactSpace M] [T2Space M] in
lemma circularPhase_mfderiv_sub (i : B.centers) (ell ell₀ : Base) (L : ℝ) (p : M) :
    (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
      (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell₀ L) p) =
      (ell.1-ell₀.1) • (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)+
        (ell.2-ell₀.2) • (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p) := by
  have h1 := ((B.circularPhase_smooth i ell L) p).mdifferentiableAt (by simp)
  have h0 := ((B.circularPhase_smooth i ell₀ L) p).mdifferentiableAt (by simp)
  have hx := ((B.circularPhase_smooth i (1,0) 0) p).mdifferentiableAt (by simp)
  have hy := ((B.circularPhase_smooth i (0,1) 0) p).mdifferentiableAt (by simp)
  erw [← mfderiv_sub h1 h0,B.circularPhase_sub]
  erw [mfderiv_add (hx.const_smul _) (hy.const_smul _),
    const_smul_mfderiv hx,const_smul_mfderiv hy]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
