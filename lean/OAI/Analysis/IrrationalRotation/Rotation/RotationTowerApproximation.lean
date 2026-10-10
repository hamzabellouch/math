import OAI.Analysis.IrrationalRotation.Analysis.TowerApproximationBounds
import OAI.Analysis.IrrationalRotation.Rotation.RotationTrace

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Invariant233.Rotation

theorem strong_tendsto_of_vacuum_of_bounded
    {ι : Type*} {l : Filter ι} (θ : ℝ)
    {A : ι → Hilbert →L[ℂ] Hilbert} {B : Hilbert →L[ℂ] Hilbert} {C : ℝ}
    (hA : ∀ i, A i ∈ algebra θ) (hB : B ∈ algebra θ)
    (hvac : Tendsto (fun i => A i vacuum) l (𝓝 (B vacuum)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (v : Hilbert) :
    Tendsto (fun i => A i v) l (𝓝 (B v)) :=
  (vacuum_faithfulTracial θ).strong_tendsto_of_bounded hA hB hvac hC v

theorem strong_tendsto_of_tower_agreement
    {ι : Type*} {l : Filter ι} (θ : ℝ)
    {A : ι → Hilbert →L[ℂ] Hilbert} {B : Hilbert →L[ℂ] Hilbert}
    {P : ι → Hilbert →L[ℂ] Hilbert}
    (hAmem : ∀ i, A i ∈ algebra θ) (hBmem : B ∈ algebra θ)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hP : ∀ i, IsStarProjection (P i)) (hagree : ∀ i, A i * P i = B * P i)
    (htrace : Tendsto (fun i => (vacuumFunctional (1 - P i)).re) l (𝓝 0))
    (v : Hilbert) : Tendsto (fun i => A i v) l (𝓝 (B v)) :=
  TowerApproximation.strong_tendsto_of_complement_trace_tendsto_zero
    (vacuum_faithfulTracial θ) hAmem hBmem hA hB hP hagree htrace v

end Invariant233.Rotation

end

end OAI
