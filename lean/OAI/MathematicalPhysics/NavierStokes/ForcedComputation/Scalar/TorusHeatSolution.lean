import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatBoundaryRegularity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatGaussianBound

namespace OAI

/-! The periodic Gaussian heat evolution solves the scalar heat equation. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem torusHeatEvolution_solution (T : ℝ) (g : Plane → ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : PlanePeriodic g) :
    TorusScalarSolution T 1 (fun _ _ => 0) (fun _ _ => 0) (torusHeatEvolution g) g := by
  refine ⟨(torusHeatEvolution_contDiffOn hg hp).mono (fun _ h => ⟨h.1.1, h.2⟩),
    fun t _ => torusHeatEvolution_periodic hp t, torusHeatEvolution_initial g, ?_⟩
  intro t ht x
  have hd := torusHeatEvolution_hasFDerivWithinAt hg hp
    (show (t,x) ∈ Ici (0 : ℝ) ×ˢ (univ : Set Plane) from ⟨ht.1, mem_univ _⟩)
  have hl : HasDerivWithinAt (fun s : ℝ => (s,x)) (1,0) (Icc 0 T) t :=
    (hasDerivAt_id t).hasDerivWithinAt.prodMk (hasDerivWithinAt_const t (Icc 0 T) x)
  have h := hd.comp_hasDerivWithinAt t hl
    (show MapsTo (fun s : ℝ => (s,x)) (Icc 0 T) (Ici (0 : ℝ) ×ˢ univ) from
      fun s hs => ⟨hs.1, mem_univ _⟩)
  change HasDerivWithinAt (fun s => torusHeatEvolution g s x) _ (Icc 0 T) t at h
  simpa only [torusHeatDerivative_apply, one_mul, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, scalarGenerator, one_mul,
    ContinuousLinearMap.map_zero, sub_zero, torusHeatEvolution_laplacian hg hp t] using h

/-- Maheux's two-dimensional periodic heat representation and Gaussian bound
for the lattice Gaussian and convolution. -/
theorem torusHeatInput : TorusHeatInput where
  continuous := fun _ ht => torusHeatKernel_continuous ht
  solution := fun T _ g hg hp => torusHeatEvolution_solution T g hg hp
  gaussian := fun _ ht x => torusHeatKernel_gaussian ht x

end ForcedComputation.VelocityDetector

end

end OAI
