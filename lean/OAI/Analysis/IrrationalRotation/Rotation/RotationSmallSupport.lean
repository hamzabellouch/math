import OAI.Analysis.IrrationalRotation.Analysis.SmallSupportStrongApproximation
import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurable
import OAI.Analysis.IrrationalRotation.Rotation.RotationFourierDensity

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.RotationSmallSupport
open Rotation

private theorem indicator_one_bound (s : Set Circle) (x : Circle) :
    ‖s.indicator (fun _ => (1 : ℂ)) x‖ ≤ (1 : ℝ) := by
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

def orbitCutoff (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) : Hilbert →L[ℂ] Hilbert :=
  measurableRepresentation θ (s.indicator (fun _ => (1 : ℂ))) 1 zero_le_one
    (measurable_const.indicator hs) (indicator_one_bound s)

theorem orbitCutoff_mem (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) :
    orbitCutoff θ s hs ∈ algebra θ :=
  measurableRepresentation_mem_algebra θ _ _ _ _ _

theorem norm_orbitCutoff_le (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) :
    ‖orbitCutoff θ s hs‖ ≤ 1 :=
  measurableRepresentation_norm_le θ _ _ _ _ _

theorem orbitCutoff_fourierCoordinate (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) (m n : ℤ) :
    orbitCutoff θ s hs (fourierCoordinate m n) =
      SmallSupport.cutoff (μ := circleMeasure) ((action θ m) ⁻¹' s)
        (hs.preimage (action_continuous θ m).measurable) (fourierCoordinate m n) := by
  apply Lp.ext
  filter_upwards [measurableRepresentation_coordinates_ae θ
      (s.indicator (fun _ => (1 : ℂ))) 1 zero_le_one
      (measurable_const.indicator hs) (indicator_one_bound s) (fourierCoordinate m n),
    L2Multiplication.multiplier_indicator_coe ((action θ m) ⁻¹' s)
      (hs.preimage (action_continuous θ m).measurable) (fourierCoordinate m n),
    fourierCoordinate_ae m n] with x hx hy hf
  change ∀ k : ℤ, orbitCutoff θ s hs (fourierCoordinate m n) x k =
    s.indicator (fun _ => (1 : ℂ)) (action θ k x) * fourierCoordinate m n x k at hx
  change SmallSupport.cutoff (μ := circleMeasure) ((action θ m) ⁻¹' s)
    (hs.preimage (action_continuous θ m).measurable) (fourierCoordinate m n) x = _ at hy
  apply lp.ext
  funext k
  change orbitCutoff θ s hs (fourierCoordinate m n) x k = _
  rw [hx k]
  change _ = (SmallSupport.cutoff (μ := circleMeasure) ((action θ m) ⁻¹' s)
    (hs.preimage (action_continuous θ m).measurable) (fourierCoordinate m n) x) k
  rw [hy, hf]
  by_cases hkm : k = m
  · subst k
    by_cases hxs : action θ m x ∈ s <;> simp [Set.indicator, hxs, Set.mem_preimage, hf]
  · by_cases hxs : action θ m x ∈ s <;>
      simp [Set.indicator, hxs, Set.mem_preimage, lp.single_apply, hkm, hf]

theorem orbitCutoff_tendsto_apply {ι : Type*} {l : Filter ι}
    (θ : ℝ) (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hμ : Tendsto (fun i => circleMeasure (s i)) l (𝓝 0)) (v : Hilbert) :
    Tendsto (fun i => orbitCutoff θ (s i) (hs i) v) l (𝓝 0) := by
  apply strong_tendsto_of_dense_span_of_bounded (A₀ := 0) (C := 1)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourierCoordinate_dense) ?_ ?_ v
  · rintro ⟨m, n⟩
    simp only [zero_apply]
    simp_rw [orbitCutoff_fourierCoordinate]
    apply SmallSupport.cutoff_tendsto_apply
    have heq : (fun i => circleMeasure ((action θ m) ⁻¹' s i)) =
        fun i => circleMeasure (s i) := by
      funext i
      exact (action_measurePreserving θ m).measure_preimage (hs i).nullMeasurableSet
    rw [heq]
    exact hμ
  · exact Eventually.of_forall fun i => norm_orbitCutoff_le θ (s i) (hs i)

theorem orbitCutoff_tendsto_strong {ι : Type*} {l : Filter ι}
    (θ : ℝ) (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hμ : Tendsto (fun i => circleMeasure (s i)) l (𝓝 0)) :
    Tendsto (fun i => UniformConvergenceCLM.ofFun (RingHom.id ℂ) Hilbert
      {t : Set Hilbert | t.Finite} (orbitCutoff θ (s i) (hs i))) l (𝓝 0) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  exact orbitCutoff_tendsto_apply θ s hs hμ

theorem tendsto_apply_of_tower_boundary {ι : Type*} {l : Filter ι}
    (θ : ℝ) (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hμ : Tendsto (fun i => circleMeasure (s i)) l (𝓝 0))
    (A : ι → Hilbert →L[ℂ] Hilbert) (B : Hilbert →L[ℂ] Hilbert) {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖A i - B‖ ≤ C)
    (hsupport : ∀ᶠ i in l, (A i - B) * (1 - orbitCutoff θ (s i) (hs i)) = 0)
    (v : Hilbert) : Tendsto (fun i => A i v) l (𝓝 (B v)) :=
  SmallSupport.tendsto_apply_of_right_supported A B _ hbound hsupport
    (orbitCutoff_tendsto_apply θ s hs hμ) v

end Invariant233.RotationSmallSupport

end

end OAI
