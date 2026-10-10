import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildTruncation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatInitialContinuity

namespace OAI

/-! The canonical initial-data and source paths for the finite-jet mild equation. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Set Filter MeasureTheory ShearFlows
open scoped Topology Interval BigOperators

/-- Strong continuity of heat evolution on any jet with one extra bounded derivative. -/
theorem initialHeat_continuousOn {ν : ℝ} (hν : 0 < ν) (k : ℕ) (J : Jet (k+1)) :
    ContinuousOn (fun t : ℝ => PlaneHeat.evolutionOperator ℝ k (ν*t)
      (BoundedSpatialJets.truncate Plane ℝ k (k+1) (by omega) J)) (Ici 0) := by
  let v := BoundedSpatialJets.truncate Plane ℝ k (k+1) (by omega) J
  have hc : ContinuousOn (fun r : ℝ => PlaneHeat.evolutionOperator ℝ k r v) (Ioi 0) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun r : Ioi (0 : ℝ) => PlaneHeat.evolutionOperator ℝ k r.val v) =
        (fun r : Ioi (0 : ℝ) => PlaneHeat.heatOperator ℝ k r.val r.property v) := by
      funext r
      have hr : 0 < r.val := r.property
      have he : PlaneHeat.evolutionOperator ℝ k r.val = PlaneHeat.heatOperator ℝ k r.val hr :=
        dite_eq_left hr
      exact congrArg (fun L : Jet k →L[ℝ] Jet k => L v) he
    change Continuous (fun r : Ioi (0 : ℝ) => PlaneHeat.evolutionOperator ℝ k r.val v)
    rw [he]
    exact (PlaneHeat.continuous_heatOperator ℝ k).clm_apply continuous_const
  intro t ht
  by_cases hz : t = 0
  · subst t
    apply ContinuousAt.continuousWithinAt
    change Tendsto (fun s : ℝ => PlaneHeat.evolutionOperator ℝ k (ν*s) v)
      (𝓝 0) (𝓝 (PlaneHeat.evolutionOperator ℝ k (ν*0) v))
    have hd := (PlaneHeat.evolutionOperator_truncate_tendsto ℝ k J).comp
      (show Tendsto (fun s : ℝ => ν*s) (𝓝 0) (𝓝 0) by
        simpa only [mul_zero] using
          (show Continuous (fun s : ℝ => ν*s) from continuous_const.mul continuous_id).tendsto (0 : ℝ))
    simpa only [Function.comp_def, v, mul_zero, PlaneHeat.evolutionOperator_initial, ContinuousLinearMap.id_apply]
      using hd
  · have hp : 0 < ν*t := mul_pos hν (lt_of_le_of_ne ht (fun h => hz h.symm))
    exact ((hc.continuousAt (Ioi_mem_nhds hp)).comp
      (f := fun s : ℝ => ν*s) (continuousAt_const.mul continuousAt_id)).continuousWithinAt

/-- The initial heat evolution as a continuous path, including time zero. -/
def initialHeatPath {T ν : ℝ} (hν : 0 < ν) (k : ℕ) (J : Jet (k+1)) :
    WeaklySingular.Path (Jet k) T :=
  (WeaklySingular.pathEquiv (Jet k) T).symm
    ⟨fun t => PlaneHeat.evolutionOperator ℝ k (ν*t.val)
        (BoundedSpatialJets.truncate Plane ℝ k (k+1) (by omega) J),
      (initialHeat_continuousOn hν k J).comp_continuous continuous_subtype_val
        (fun t => t.property.1)⟩

@[simp] theorem initialHeatPath_apply {T ν : ℝ} (hν : 0 < ν) (k : ℕ)
    (J : Jet (k+1)) (t : Icc (0 : ℝ) T) :
    initialHeatPath (T := T) hν k J t = PlaneHeat.evolutionOperator ℝ k (ν*t.val)
      (BoundedSpatialJets.truncate Plane ℝ k (k+1) (by omega) J) := rfl

/-- The artificial positive-time cutoff disappears on the finite integration interval. -/
def heatSourcePath {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (k : ℕ)
    (g : WeaklySingular.Path (Jet k) T) : WeaklySingular.Path (Jet k) T :=
  WeaklySingular.integralOperator (Jet k) hT (heatKernel hν k T)
    (heatKernel_continuous hν k T) (Real.sqrt (T+1)) (Real.sqrt_nonneg _)
    (heatKernel_bound hν k T) g

@[simp] theorem heatSourcePath_apply {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (k : ℕ)
    (g : WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    heatSourcePath hT hν k g t = ∫ s in 0..t.val,
      rawHeatKernel hν k (t.val-s) (WeaklySingular.extendPath (Jet k) hT g s) := by
  change (∫ s in 0..t.val, heatKernel hν k T (t.val-s)
    (WeaklySingular.extendPath (Jet k) hT g s)) = _
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  exact congrArg (fun L : Jet k →L[ℝ] Jet k => L
    (WeaklySingular.extendPath (Jet k) hT g s))
    (heatKernel_eq_raw hν k ((sub_le_self _ hs.1).trans t.property.2))

/-- Heat evolution and truncation commute also at the initial time. -/
theorem evolutionOperator_truncate (k n : ℕ) (hkn : k ≤ n) (r : ℝ) (J : Jet n) :
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn
      (PlaneHeat.evolutionOperator ℝ n r J) =
      PlaneHeat.evolutionOperator ℝ k r (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn J) := by
  by_cases hr : 0 < r
  · simp only [PlaneHeat.evolutionOperator, dite_eq_left hr]
    exact (BoundedSpatialJets.convolution_truncate Plane ℝ k n hkn volume
      (PlaneHeat.kernel r) (PlaneHeat.kernel_integrable hr) J).symm
  · simp only [PlaneHeat.evolutionOperator, dite_eq_right hr, ContinuousLinearMap.id_apply]

/-- The inhomogeneous source path is compatible with every finite-order truncation. -/
theorem heatSourcePath_truncate {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k n : ℕ) (hkn : k ≤ n) (g : WeaklySingular.Path (Jet n) T) :
    truncatePath k n hkn T (heatSourcePath hT hν n g) =
      heatSourcePath hT hν k (truncatePath k n hkn T g) := by
  apply (WeaklySingular.pathEquiv (Jet k) T).injective
  apply ContinuousMap.ext
  intro t
  change BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (heatSourcePath hT hν n g t) = _
  simp only [heatSourcePath_apply]
  exact rawKernelIntegral_truncate hT hν k n hkn g 0 t

/-- The initial paths inherit compatibility from their initial jets. -/
theorem initialHeatPath_truncate {T ν : ℝ} (hν : 0 < ν)
    (k n : ℕ) (hkn : k ≤ n) (J : Jet (n+1)) (K : Jet (k+1))
    (hJK : BoundedSpatialJets.truncateCLM Plane ℝ k n hkn
      (BoundedSpatialJets.truncate Plane ℝ n (n+1) (by omega) J) =
      BoundedSpatialJets.truncate Plane ℝ k (k+1) (by omega) K) :
    truncatePath k n hkn T (initialHeatPath hν n J) = initialHeatPath hν k K := by
  apply (WeaklySingular.pathEquiv (Jet k) T).injective
  apply ContinuousMap.ext
  intro t
  change BoundedSpatialJets.truncateCLM Plane ℝ k n hkn
    (PlaneHeat.evolutionOperator ℝ n (ν*t.val)
      (BoundedSpatialJets.truncate Plane ℝ n (n+1) (by omega) J)) = _
  exact (evolutionOperator_truncate k n hkn (ν*t.val) _).trans
    (congrArg (PlaneHeat.evolutionOperator ℝ k (ν*t.val)) hJK)

/-- The actual affine forcing path in the scalar variation-of-constants equation. -/
def forcingPath {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (k : ℕ)
    (J : Jet (k+1)) (g : WeaklySingular.Path (Jet k) T) :
    WeaklySingular.Path (Jet k) T := initialHeatPath hν k J + heatSourcePath hT hν k g

@[simp] theorem forcingPath_apply {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (k : ℕ)
    (J : Jet (k+1)) (g : WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    forcingPath hT hν k J g t =
      PlaneHeat.evolutionOperator ℝ k (ν*t.val)
        (BoundedSpatialJets.truncate Plane ℝ k (k+1) (by omega) J) +
      ∫ s in 0..t.val, rawHeatKernel hν k (t.val-s)
        (WeaklySingular.extendPath (Jet k) hT g s) := by
  change initialHeatPath hν k J t + heatSourcePath hT hν k g t = _
  rw [initialHeatPath_apply, heatSourcePath_apply]

/-- Canonical forcing paths retain compatibility at every spatial derivative order. -/
theorem forcingPath_truncate {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k n : ℕ) (hkn : k ≤ n) (J : Jet (n+1)) (K : Jet (k+1))
    (hJK : BoundedSpatialJets.truncateCLM Plane ℝ k n hkn
      (BoundedSpatialJets.truncate Plane ℝ n (n+1) (by omega) J) =
      BoundedSpatialJets.truncate Plane ℝ k (k+1) (by omega) K)
    (g : WeaklySingular.Path (Jet n) T) :
    truncatePath k n hkn T (forcingPath hT hν n J g) =
      forcingPath hT hν k K (truncatePath k n hkn T g) := by
  change truncatePath k n hkn T (initialHeatPath hν n J + heatSourcePath hT hν n g) = _
  rw [map_add, initialHeatPath_truncate hν k n hkn J K hJK, heatSourcePath_truncate]
  rfl

end ForcedComputation.PlaneScalarMild

end

end OAI
