import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPlanarFlow
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarReverseVariations

namespace OAI

/-! Quantitative estimates for the compact planar extension, assuming the
variational equations for the actual periodic transition map. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian Set Filter
open scoped Topology

theorem compactTransition_germ (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ Ω : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω)
    {x : Plane} (hx : ∀ j : Fin 2, 0 < x j ∧ x j < 1) (a t : ℝ) :
    Ψ a t =ᶠ[𝓝 x] Ω a t := by
  have ho : IsOpen {y : Plane | ∀ j : Fin 2, 0 < y j ∧ y j < 1} := by
    have he : {y : Plane | ∀ j : Fin 2, 0 < y j ∧ y j < 1} =
        ⋂ j : Fin 2, (fun y : Plane => y j) ⁻¹' Ioo 0 1 := by
      ext y
      simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_Ioo]
    rw [he]
    exact isOpen_iInter_of_finite (fun j => isOpen_Ioo.preimage (continuous_apply j))
  filter_upwards [ho.mem_nhds hx] with y hy
  exact compactTransition_eq_slice I hI hΨ hΩ hy a t

theorem compactTransition_germ_id (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ)
    {x : Plane} (hx : x ∉ commonSupport (normalizedPulse I hI)) (a t : ℝ) :
    Ψ a t =ᶠ[𝓝 x] id := by
  have ho := (commonSupport_compact (normalizedPulse I hI)).isClosed.isOpen_compl
  filter_upwards [ho.mem_nhds hx] with y hy
  exact compactTransition_fixed I hI hΨ hy a t

theorem compactTransition_derivative_bounds (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ Ω : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω)
    (hv : PlanarVariations (planarSlice (normalizedHamiltonian I hI)) Ω)
    (a : ℝ) (x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ a t) x‖ ≤ Real.exp ((planarFlowBound (normalizedHamiltonian I hI) : ℝ) * t) ∧
    ‖fderiv ℝ (fderiv ℝ (Ψ a t)) x‖ ≤
      Real.exp (2 * (planarFlowBound (normalizedHamiltonian I hI) : ℝ) * t) -
        Real.exp ((planarFlowBound (normalizedHamiltonian I hI) : ℝ) * t) := by
  by_cases hx : x ∈ commonSupport (normalizedPulse I hI)
  · have hg := compactTransition_germ I hI hΨ hΩ
      (commonSupport_in_unit (normalizedPulse_inUnit I hI) hx) a t
    rw [hg.fderiv.self_of_nhds, hg.fderiv.fderiv.self_of_nhds]
    exact planar_quantitative_variations (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI) hv a x ht
  · have hg := compactTransition_germ_id I hI hΨ hx a t
    have hi : fderiv ℝ (id : Plane → Plane) = fun _ => ContinuousLinearMap.id ℝ Plane :=
      funext fun _ => fderiv_id
    have hz : fderiv ℝ (fderiv ℝ (id : Plane → Plane)) x = 0 := by
      rw [hi]
      exact fderiv_const_apply (ContinuousLinearMap.id ℝ Plane)
    have hL : (0 : ℝ) ≤ planarFlowBound (normalizedHamiltonian I hI) := Nat.cast_nonneg _
    constructor
    · rw [hg.fderiv.self_of_nhds, fderiv_id]
      exact (ContinuousLinearMap.norm_id_le).trans (Real.one_le_exp (mul_nonneg hL ht))
    · rw [hg.fderiv.fderiv.self_of_nhds, hz]
      have hn : ‖(0 : Plane →L[ℝ] (Plane →L[ℝ] Plane))‖ = 0 :=
        ContinuousLinearMap.opNorm_zero
      rw [hn]
      apply sub_nonneg.mpr
      apply Real.exp_le_exp.mpr
      nlinarith

end ForcedComputation.Recorder.Planar

end

end OAI
