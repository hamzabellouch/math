import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialL2
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

/-! # Radial Schwartz derivatives are Cartesian tensor contractions

This is the dense-domain identity for the completed radial derivative.
-/

open MeasureTheory Set LineDeriv
open scoped SchwartzMap LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- The ordinary radial derivative is the contraction of the Cartesian jet
against the unit vector, with no lower-order correction terms. -/
theorem schwartz_radial_iteratedDeriv (N : ℕ) (f : 𝓢(E, ℂ))
    (ω : PhysicalUnitSphere) (r : ℝ) :
    iteratedDeriv N (fun t : ℝ => f (t • ω.1)) r =
      ∑ j : Fin N → Fin 12,
        (radialTensorCoefficient N j ω : ℂ) *
          homogeneousOrderedDerivative N j f (r • ω.1) := by
  have hw : ‖ω.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using ω.2
  let L : ℝ →L[ℝ] E := (LinearIsometry.toSpanSingleton ℝ E hw).toContinuousLinearMap
  have hL := L.iteratedFDeriv_comp_right (f.smooth ⊤) r (i := N) (by simp)
  have hjet : iteratedDeriv N (fun t : ℝ => f (t • ω.1)) r =
      iteratedFDeriv ℝ N f (r • ω.1) (fun _ => ω.1) := by
    change iteratedFDeriv ℝ N (f ∘ L) r (fun _ => (1 : ℝ)) = _
    rw [hL]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      L, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.toSpanSingleton_apply,
      one_smul]
  rw [hjet]
  have hb : (∑ j : Fin 12, ω.1 j • (EuclideanSpace.basisFun (Fin 12) ℝ) j) = ω.1 := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin 12) ℝ).sum_repr ω.1
  calc
    _ = iteratedFDeriv ℝ N f (r • ω.1)
        (fun _ : Fin N => ∑ j : Fin 12, ω.1 j • (EuclideanSpace.basisFun (Fin 12) ℝ) j) := by
      rw [hb]
    _ = ∑ j : Fin N → Fin 12, (∏ i, ω.1 (j i)) •
        iteratedFDeriv ℝ N f (r • ω.1)
          (fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j i)) := by
      rw [ContinuousMultilinearMap.map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact ContinuousMultilinearMap.map_smul_univ _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
      rfl


end DefocusingNLS

end OAI
