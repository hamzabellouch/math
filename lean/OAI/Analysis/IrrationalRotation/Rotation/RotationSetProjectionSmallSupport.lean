import OAI.Analysis.IrrationalRotation.Rotation.RotationSmallSupportBounds
import OAI.Analysis.IrrationalRotation.Rotation.RotationDiffuse

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.RotationSmallSupport

@[simp] theorem orbitCutoff_eq_borelSetProjection (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) : orbitCutoff θ s hs = Rotation.borelSetProjection θ s hs := rfl

end Invariant233.RotationSmallSupport

namespace Invariant233.Rotation

theorem borelSetProjection_tendsto_apply {ι : Type*} {l : Filter ι}
    (θ : ℝ) (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hμ : Tendsto (fun i => circleMeasure (s i)) l (𝓝 0)) (v : Hilbert) :
    Tendsto (fun i => borelSetProjection θ (s i) (hs i) v) l (𝓝 0) :=
  RotationSmallSupport.orbitCutoff_tendsto_apply θ s hs hμ v

theorem norm_borelSetProjection_fourierCoordinate (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) (m n : ℤ) :
    ‖borelSetProjection θ s hs (fourierCoordinate m n)‖ = Real.sqrt (circleMeasure.real s) :=
  RotationSmallSupport.norm_orbitCutoff_fourierCoordinate θ s hs m n

theorem tendsto_apply_of_small_borel_boundary {ι : Type*} {l : Filter ι}
    (θ : ℝ) (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hμ : Tendsto (fun i => circleMeasure (s i)) l (𝓝 0))
    (A : ι → Hilbert →L[ℂ] Hilbert) (B : Hilbert →L[ℂ] Hilbert) {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖A i - B‖ ≤ C)
    (hsupport : ∀ᶠ i in l, (A i - B) * (1 - borelSetProjection θ (s i) (hs i)) = 0)
    (v : Hilbert) : Tendsto (fun i => A i v) l (𝓝 (B v)) :=
  RotationSmallSupport.tendsto_apply_of_tower_boundary θ s hs hμ A B hbound hsupport v

end Invariant233.Rotation

end

end OAI
