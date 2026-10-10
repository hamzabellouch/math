import OAI.Geometry.EinsteinFour.FrameFlow
import OAI.Geometry.EinsteinFour.FrameOrientation
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! Continuous frame curves stay in the same orientation component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

/-- Orientation membership is constant along a continuous real frame curve. -/
theorem FrameOrientation.mem_iff_of_continuous_curve (o : FrameOrientation g)
    (γ : ℝ → FrameBundle g) (hγ : Continuous γ) (s t : ℝ) :
    γ s ∈ o.positive ↔ γ t ∈ o.positive := by
  have hc : IsClopen (γ ⁻¹' o.positive) := o.clopen.preimage hγ
  constructor
  · intro hs
    have he : γ ⁻¹' o.positive = univ := hc.eq_univ ⟨s, hs⟩
    change t ∈ γ ⁻¹' o.positive
    rw [he]
    exact mem_univ t
  · intro ht
    have he : γ ⁻¹' o.positive = univ := hc.eq_univ ⟨t, ht⟩
    change s ∈ γ ⁻¹' o.positive
    rw [he]
    exact mem_univ s

/-- A continuous frame flow initialized at the identity preserves each
orientation component, independently of measure preservation. -/
theorem FrameFlow.orientation_preserving {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hzero : ∀ e, φ.map 0 e = e) (o : FrameOrientation g)
    (t : ℝ) (e : FrameBundle g) :
    φ.map t e ∈ o.positive ↔ e ∈ o.positive := by
  have hγ : Continuous (fun s : ℝ => φ.map s e) :=
    φ.continuous.comp (continuous_id.prodMk continuous_const)
  simpa only [hzero] using o.mem_iff_of_continuous_curve (fun s => φ.map s e) hγ t 0

end
end PositiveEinsteinFour.Geometry

end OAI
