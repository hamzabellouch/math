import OAI.Geometry.SurfaceImmersion.Atlas.TensorChartRead

namespace OAI

/-! Actual cutoff square-root amplitudes for global symmetric tensors.
Their squared phase tensors give the exact global atlas decomposition. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry
open JetPolynomial (Base)

local instance rootPhaseFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance rootPhaseFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance rootPhaseDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance rootPhaseDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance rootPhaseSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance rootPhaseSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def rootPhaseAmplitude (i : A.centers) (Q : Tensor →L[ℝ] ℝ) (w : ℝ)
    (u : ∀ x : M, CovariantTwoTensor x) : M → ℝ :=
  fun p => A.weight i p * (Real.sqrt (Q (A.tensorChartRead i u (chart (i : M) p))) / w)

lemma rootPhaseAmplitude_support (i : A.centers) (Q : Tensor →L[ℝ] ℝ) (w : ℝ)
    (u : ∀ x : M, CovariantTwoTensor x) :
    tsupport (A.rootPhaseAmplitude i Q w u) ⊆ tsupport (A.weight i) := tsupport_mul_subset_left

variable [CompactSpace M]

lemma rootPhaseAmplitude_smooth (i : A.centers) (Q : Tensor →L[ℝ] ℝ) (w : ℝ)
    {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hpos : ∀ p ∈ tsupport (A.weight i), 0 < Q (A.tensorChartRead i u (chart (i : M) p))) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.rootPhaseAmplitude i Q w u) := by
  apply contMDiff_of_tsupport
  intro p hp
  have hpw := A.rootPhaseAmplitude_support i Q w u hp
  have hc := ((chart_smooth (i : M)) p (A.weight_support i hpw)).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds (A.weight_support i hpw))
  have hr := (A.tensorChartRead_smooth i hu).contMDiff.contMDiffAt.comp p hc
  have hQ := Q.contDiff.contMDiff.contMDiffAt.comp p hr
  have hroot := (Real.contDiffAt_sqrt (ne_of_gt (hpos p hpw))).contMDiffAt.comp p hQ
  exact (A.weight_smooth i p).mul (hroot.div_const w)

omit [CompactSpace M] in
lemma rootPhaseAmplitude_square (P : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (u : ∀ x : M, CovariantTwoTensor x) (i : A.centers) (j : Fin 3)
    (hw : w i j ≠ 0)
    (hpos : ∀ p ∈ tsupport (A.weight i), 0 ≤ (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    (A.rootPhaseAmplitude i ((P i).Q j) (w i j) u p)^2 * (w i j)^2 =
      A.phaseCoefficient P u i j (chart (i : M) p) := by
  unfold phaseCoefficient
  rw [A.tensorEncode_read i u hp, map_smul]
  by_cases hz : A.weight i p = 0
  · simp [rootPhaseAmplitude, hz]
  · dsimp only [rootPhaseAmplitude]
    rw [mul_pow, div_pow, Real.sq_sqrt (hpos p (subset_tsupport _ hz))]
    simp only [smul_eq_mul]
    field_simp [hw]

omit [CompactSpace M] in
lemma restored_rootPhase (P : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (u : ∀ x : M, CovariantTwoTensor x) (i : A.centers) (j : Fin 3)
    (hw : w i j ≠ 0)
    (hpos : ∀ p ∈ tsupport (A.weight i), 0 ≤ (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (p : M) :
    ((A.rootPhaseAmplitude i ((P i).Q j) (w i j) u p)^2 * (w i j)^2) •
      A.bundleRestore A.tensorTriv i (fun _ => fiberFromThree (covectorSquare ((P i).ξ j))) p =
      A.bundleRestore A.tensorTriv i (A.phaseTensor P u i j) p := by
  by_cases hp : p ∈ (chart (i : M)).source
  · rw [A.rootPhaseAmplitude_square P w u i j hw hpos hp]
    simp only [bundleRestore, phaseTensor, map_smul, smul_smul]
    rw [mul_comm]
  · have ho : A.outer i p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (A.outer_support i h))
    simp only [bundleRestore, ho, zero_smul, smul_zero]

omit [CompactSpace M] in
/-- No positive-definiteness assumption is hidden here: only the explicitly
listed phase coefficients must be nonnegative on their supports. -/
theorem global_rootPhase_decomposition (P : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (u : ∀ x : M, CovariantTwoTensor x) (hu : ∀ p v v', u p v v' = u p v' v)
    (hw : ∀ i j, w i j ≠ 0)
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 ≤ (P i).Q j (A.tensorChartRead i u (chart (i : M) p))) (p : M) :
    (∑ i : A.centers, ∑ j : Fin 3,
      ((A.rootPhaseAmplitude i ((P i).Q j) (w i j) u p)^2 * (w i j)^2) •
        A.bundleRestore A.tensorTriv i (fun _ => fiberFromThree (covectorSquare ((P i).ξ j))) p) =
      u p := by
  simp_rw [A.restored_rootPhase P w u _ _ (hw _ _) (hpos _ _)]
  exact A.global_phase_tensor_decomposition P hu p

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
