import OAI.Geometry.Immersion.ClosedSurface.MetricAmplitude
import OAI.Geometry.Immersion.ClosedSurface.MetricCoordinates

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Bundle Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


def scalarDifferential (f : M → ℝ) (q : M) : TangentSpace planeModel q →L[ℝ] ℝ :=
  mfderiv planeModel 𝓘(ℝ) f q

def tensorEvaluate (v w : SmallModes.Base) : PhaseMean.Tensor →ₗ[ℝ] ℝ where
  toFun H := PhaseMean.evaluate H v w
  map_add' H K := by simp [PhaseMean.evaluate]; ring
  map_smul' c H := by simp [PhaseMean.evaluate,smul_eq_mul]; ring

lemma tensorEvaluate_apply (H : PhaseMean.Tensor) (v w : SmallModes.Base) :
    tensorEvaluate v w H = PhaseMean.evaluate H v w := rfl



theorem metricPhaseAmplitude_tangent_decomposition (g : SmoothMetric M) (p : M)
    (P : PhaseBasis) (χ : M → ℝ) (w : Fin 3 → ℝ)
    (hsource : tsupport χ ⊆ (coordinateChart p).source)
    (hw : ∀ j, w j ≠ 0)
    (hpos : ∀ q ∈ tsupport χ, ∀ j, 0 ≤ P.Q j (coordinateMetric g p (coordinateChart p q)))
    (q : M) (v u : TangentSpace planeModel q) :
    ∑ j, (metricPhaseAmplitude g p (P.Q j) χ (w j) q)^2 *
      (scalarDifferential (atlasPhase p (w j • P.ξ j)) q v : ℝ) *
      (scalarDifferential (atlasPhase p (w j • P.ξ j)) q u : ℝ) =
      (χ q)^2 * g.inner q v u := by
  by_cases hqs : q ∈ (coordinateChart p).source
  · let D : TangentSpace planeModel q →L[ℝ] SmallModes.Base :=
      mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q
    have he := congrArg (tensorEvaluate (D v) (D u))
      (metricPhaseAmplitude_decomposition g p P χ w hw hpos q)
    simp only [map_sum,map_smul,smul_eq_mul,tensorEvaluate_apply,covectorSquare_evaluate] at he
    have hmetric : PhaseMean.evaluate (coordinateMetric g p (coordinateChart p q))
        (D v) (D u) = g.inner q v u := coordinateMetric_pullback_chart g p hqs v u
    rw [hmetric] at he
    have hphase (ξ : SmallModes.Base) (z : TangentSpace planeModel q) :
        scalarDifferential (atlasPhase p ξ) q z = phaseLinear ξ (D z) :=
      congrArg (fun L : TangentSpace planeModel q →L[ℝ] ℝ => L z)
        (mfderiv_atlasPhase p ξ hqs)
    simp only [hphase, mul_assoc]
    exact he
  · have hχq : χ q = 0 := by
      by_contra H
      exact hqs (hsource (subset_tsupport χ H))
    simp [metricPhaseAmplitude,hχq]






theorem global_metric_phase_decomposition {ι : Type*} [Fintype ι]
    (g : SmoothMetric M) (p : ι → M) (P : ι → PhaseBasis)
    (χ : ι → M → ℝ) (w : ι → Fin 3 → ℝ)
    (hχ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (χ i))
    (hcompact : ∀ i, HasCompactSupport (χ i))
    (hsource : ∀ i, tsupport (χ i) ⊆ (coordinateChart (p i)).source)
    (hsquare : ∀ q, ∑ i, (χ i q)^2 = 1)
    (hw : ∀ i j, w i j ≠ 0)
    (hpos : ∀ i q, q ∈ tsupport (χ i) → ∀ j,
      0 < (P i).Q j (coordinateMetric g (p i) (coordinateChart (p i) q))) :
    (∀ i j, ContMDiff planeModel 𝓘(ℝ) ∞ (metricPhaseAmplitude g (p i) ((P i).Q j) (χ i) (w i j))) ∧
    (∀ i j, HasCompactSupport (metricPhaseAmplitude g (p i) ((P i).Q j) (χ i) (w i j))) ∧
    ∀ (q : M) (v u : TangentSpace planeModel q),
      ∑ i, ∑ j, (metricPhaseAmplitude g (p i) ((P i).Q j) (χ i) (w i j) q)^2 *
        (scalarDifferential (atlasPhase (p i) (w i j • (P i).ξ j)) q v : ℝ) *
        (scalarDifferential (atlasPhase (p i) (w i j • (P i).ξ j)) q u : ℝ) = g.inner q v u := by
  refine ⟨fun i j => metricPhaseAmplitude_smooth g (p i) ((P i).Q j) (χ i) (w i j)
    (hχ i) (hsource i) (fun q hq => hpos i q hq j),
    fun i j => metricPhaseAmplitude_hasCompactSupport g (p i) ((P i).Q j) (χ i) (w i j) (hcompact i),?_⟩
  intro q v u
  calc
    _ = ∑ i, (χ i q)^2 * g.inner q v u := by
      apply Finset.sum_congr rfl
      intro i _
      exact metricPhaseAmplitude_tangent_decomposition g (p i) (P i) (χ i) (w i)
        (hsource i) (hw i) (fun q hq j => (hpos i q hq j).le) q v u
    _ = (∑ i, (χ i q)^2) * g.inner q v u := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [hsquare,one_mul]

end ClosedSurfaceR4

end

end OAI
