import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPlanarBounds

namespace OAI

/-! The compact planar flow fixes every point off its common support and
preserves that support. In particular, its trajectories cannot leave the
unit-square chart. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian Set

theorem compactTransition_fixed (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ) {x : Plane}
    (hx : x ∉ commonSupport (normalizedPulse I hI)) (a t : ℝ) : Ψ a t x = x := by
  symm
  apply hΨ.unique a x (fun _ => x) rfl
  intro s
  have hn : x ∉ tsupport (compactVelocity I hI (a + s)) :=
    fun h => hx (compactVelocity_support I hI (a + s) h)
  rw [image_eq_zero_of_notMem_tsupport hn]
  exact hasDerivAt_const s x

theorem compactTransition_support (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ) {x : Plane}
    (hx : x ∈ commonSupport (normalizedPulse I hI)) (a t : ℝ) :
    Ψ a t x ∈ commonSupport (normalizedPulse I hI) := by
  by_contra hn
  have he := compactTransition_fixed I hI hΨ hn a t
  have hxy : x = Ψ a t x := (hΨ.bijective a t).1 he.symm
  exact hn (hxy ▸ hx)

theorem compactTransition_chart (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ) {x : Plane}
    (hx : ∀ j : Fin 2, 0 < x j ∧ x j < 1) (a t : ℝ) :
    ∀ j : Fin 2, 0 < Ψ a t x j ∧ Ψ a t x j < 1 := by
  by_cases hm : x ∈ commonSupport (normalizedPulse I hI)
  · exact commonSupport_in_unit (normalizedPulse_inUnit I hI)
      (compactTransition_support I hI hΨ hm a t)
  · rw [compactTransition_fixed I hI hΨ hm a t]
    exact hx

theorem compactTransition_eq_slice (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ Ω : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω)
    {x : Plane} (hx : ∀ j : Fin 2, 0 < x j ∧ x j < 1) (a t : ℝ) :
    Ψ a t x = Ω a t x := by
  apply hΩ.unique a x (fun s => Ψ a s x) (hΨ.initial a x)
  intro s
  have hy := compactTransition_chart I hI hΨ hx a s
  have he := normalized_planar_field_on_chart I hI (a + s) (Ψ a s x) (hy 0) (hy 1)
  exact (hΨ.ode a s x).congr_deriv he

end ForcedComputation.Recorder.Planar

end

end OAI
