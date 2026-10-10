import OAI.Geometry.SurfaceImmersion.Atlas.TensorPhaseDifferential
import OAI.Geometry.Immersion.ClosedSurface.TangentDecomposition

namespace OAI

/-! The global cutoff amplitudes give the actual rank-one phase differentials
needed for the quadratic oscillatory construction. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry

local instance globalAmplitudeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance globalAmplitudeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance globalAmplitudeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance globalAmplitudeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance globalAmplitudeSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance globalAmplitudeSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem global_tensor_amplitude_decomposition (P : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ∀ p v v', u p v v' = u p v' v) (hw : ∀ i j, w i j ≠ 0)
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 ≤ (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (p : M) (v v' : TangentSpace planeModel p) :
    (∑ i : A.centers, ∑ j : Fin 3,
      (A.rootPhaseAmplitude i ((P i).Q j) (w i j) u p)^2 *
        scalarDifferential (atlasPhase (i : M) (w i j • (P i).ξ j)) p v *
        scalarDifferential (atlasPhase (i : M) (w i j • (P i).ξ j)) p v') = u p v v' := by
  have hh := congrArg (fun B : CovariantTwoTensor p => B v v')
    (A.global_rootPhase_decomposition P w u hu hw hpos p)
  calc
    _ = ∑ i : A.centers, ∑ j : Fin 3,
        ((A.rootPhaseAmplitude i ((P i).Q j) (w i j) u p)^2 * (w i j)^2) *
          A.bundleRestore A.tensorTriv i
            (fun _ => fiberFromThree (covectorSquare ((P i).ξ j))) p v v' := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hz : A.rootPhaseAmplitude i ((P i).Q j) (w i j) u p = 0
      · simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul]
      · have hweight : A.weight i p ≠ 0 := by
          intro he
          apply hz
          simp only [rootPhaseAmplitude, he, zero_mul]
        have hsupport := subset_tsupport (A.weight i) hweight
        have hp := A.weight_support i hsupport
        have hp' : p ∈ (coordinateChart (i : M)).source := by
          simpa only [coordinateChart_source, chart_source] using hp
        rw [A.tensorRestore_covectorSquare i _ hp, A.outer_one i p hsupport]
        have hscaled (z : TangentSpace planeModel p) :
            scalarDifferential (atlasPhase (i : M) (w i j • (P i).ξ j)) p z =
              w i j * (show ℝ from mfderiv planeModel 𝓘(ℝ) (atlasPhase (i : M) ((P i).ξ j)) p z) := by
          let D : TangentSpace planeModel p →L[ℝ] SmallModes.Base :=
            mfderiv planeModel 𝓘(ℝ, SmallModes.Base) (coordinateChart (i : M)) p
          unfold scalarDifferential
          rw [mfderiv_atlasPhase _ _ hp', mfderiv_atlasPhase _ _ hp']
          change phaseLinear (w i j • (P i).ξ j)
              (D z) =
            w i j * phaseLinear ((P i).ξ j)
              (D z)
          simp only [phaseLinear_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          ring
        rw [hscaled v, hscaled v']
        ring
    _ = _ := by
      simpa only [sum_apply, smul_apply, smul_eq_mul] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
