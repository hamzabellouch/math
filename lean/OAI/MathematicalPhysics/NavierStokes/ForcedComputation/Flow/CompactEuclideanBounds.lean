import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPlanarVariations
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.EuclideanFlowBounds

namespace OAI

/-! The Euclidean estimates also hold for the compact extension. In the
chart its transition is locally the periodic transition, and outside the
common support its transition is locally the identity. -/

noncomputable section
namespace ForcedComputation

open ShearFlows PlanarHamiltonian Set Filter
open scoped Topology ContDiff

theorem euclideanMap_eventuallyEq {f g : Plane → Plane} {x : EuclideanPlane}
    (h : f =ᶠ[𝓝 (planeCoordinates x)] g) :
    euclideanMap f =ᶠ[𝓝 x] euclideanMap g := by
  have hh := h.comp_tendsto (planeCoordinates.continuous.continuousAt.tendsto)
  exact hh.mono (fun y hy => congrArg planeCoordinates.symm hy)

namespace Recorder.Planar

theorem compact_euclidean_field_bounds (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (s : ℝ) (x : EuclideanPlane) :
    ‖fderiv ℝ (euclideanMap (compactVelocity I hI s)) x‖ ≤
        (euclideanFlowBound (normalizedHamiltonian I hI) : ℝ) ∧
    ‖fderiv ℝ (fderiv ℝ (euclideanMap (compactVelocity I hI s))) x‖ ≤
        (euclideanFlowBound (normalizedHamiltonian I hI) : ℝ) := by
  by_cases hx : (planeCoordinates x) 0 ∈ Ioo (0 : ℝ) 1 ∧
      (planeCoordinates x) 1 ∈ Ioo (0 : ℝ) 1
  · have he := euclideanMap_eventuallyEq (compactVelocity_germ I hI s hx.1 hx.2)
    rw [he.fderiv.self_of_nhds, he.fderiv.fderiv.self_of_nhds]
    exact euclidean_field_bounds (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI) s x
  · have hz := compactVelocity_off_chart I hI s hx
    rw [notMem_tsupport_iff_eventuallyEq] at hz
    have he : euclideanMap (compactVelocity I hI s) =ᶠ[𝓝 x]
        (fun _ : EuclideanPlane => (0 : EuclideanPlane)) := by
      filter_upwards [hz.comp_tendsto planeCoordinates.continuous.continuousAt.tendsto]
        with y hy
      change compactVelocity I hI s (planeCoordinates y) = 0 at hy
      change planeCoordinates.symm (compactVelocity I hI s (planeCoordinates y)) = 0
      rw [hy]
      exact planeCoordinates.symm.map_zero
    rw [he.fderiv.self_of_nhds, he.fderiv.fderiv.self_of_nhds]
    constructor
    · rw [fderiv_const_apply, ContinuousLinearMap.opNorm_zero]
      exact Nat.cast_nonneg _
    · have hf : fderiv ℝ (fun _ : EuclideanPlane => (0 : EuclideanPlane)) =
          fun _ => (0 : EuclideanPlane →L[ℝ] EuclideanPlane) := by
        funext z
        exact fderiv_const_apply _
      rw [hf, fderiv_const_apply, ContinuousLinearMap.opNorm_zero]
      exact Nat.cast_nonneg _

theorem compactTransition_euclidean_germ (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ Ω : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω)
    (a t : ℝ) (x : EuclideanPlane) :
    (euclideanMap (Ψ a t) =ᶠ[𝓝 x] euclideanMap (Ω a t)) ∨
      (euclideanMap (Ψ a t) =ᶠ[𝓝 x] id) := by
  by_cases hx : planeCoordinates x ∈ commonSupport (normalizedPulse I hI)
  · exact Or.inl (euclideanMap_eventuallyEq (compactTransition_germ I hI hΨ hΩ
      (commonSupport_in_unit (normalizedPulse_inUnit I hI) hx) a t))
  · right
    have hh := euclideanMap_eventuallyEq (compactTransition_germ_id I hI hΨ hx a t)
    have hid : euclideanMap (id : Plane → Plane) = id := by
      funext y
      exact planeCoordinates.symm_apply_apply y
    rwa [hid] at hh

theorem compactTransition_euclidean_smooth (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ Ω : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω)
    (hv : PlanarVariations (planarSlice (normalizedHamiltonian I hI)) Ω)
    (a t : ℝ) : ContDiff ℝ ∞ (euclideanMap (Ψ a t)) := by
  have hs := (hv.euclidean (fun s => planarSlice_smooth (normalizedHamiltonian_valid I hI) s)).smooth a t
  apply contDiff_iff_contDiffAt.mpr
  intro x
  rcases compactTransition_euclidean_germ I hI hΨ hΩ a t x with h | h
  · exact hs.contDiffAt.congr_of_eventuallyEq h
  · exact contDiff_id.contDiffAt.congr_of_eventuallyEq h

theorem compactTransition_euclidean_transfer (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ Ω : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω)
    (a t : ℝ) {B₁ B₂ : ℝ} (hB₁ : 1 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb : ∀ x, ‖fderiv ℝ (euclideanMap (Ω a t)) x‖ ≤ B₁ ∧
      ‖fderiv ℝ (fderiv ℝ (euclideanMap (Ω a t))) x‖ ≤ B₂) (x : EuclideanPlane) :
    ‖fderiv ℝ (euclideanMap (Ψ a t)) x‖ ≤ B₁ ∧
      ‖fderiv ℝ (fderiv ℝ (euclideanMap (Ψ a t))) x‖ ≤ B₂ := by
  rcases compactTransition_euclidean_germ I hI hΨ hΩ a t x with h | h
  · rw [h.fderiv.self_of_nhds, h.fderiv.fderiv.self_of_nhds]
    exact hb x
  · have hid : fderiv ℝ (id : EuclideanPlane → EuclideanPlane) =
        fun _ => ContinuousLinearMap.id ℝ EuclideanPlane := funext fun _ => fderiv_id
    constructor
    · rw [h.fderiv.self_of_nhds, fderiv_id]
      exact ContinuousLinearMap.norm_id_le.trans hB₁
    · rw [h.fderiv.fderiv.self_of_nhds, hid, fderiv_const_apply]
      rw [ContinuousLinearMap.opNorm_zero]
      exact hB₂

theorem compact_euclidean_flow_estimates (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ Ω : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω)
    (hv : PlanarVariations (planarSlice (normalizedHamiltonian I hI)) Ω)
    (a t : ℝ) (ht : 0 ≤ t) :
    (∀ x, (‖fderiv ℝ (euclideanMap (Ψ a t)) x‖ ≤
        Real.exp ((euclideanFlowBound (normalizedHamiltonian I hI) : ℝ) * t) ∧
      ‖fderiv ℝ (fderiv ℝ (euclideanMap (Ψ a t))) x‖ ≤
        Real.exp (2 * (euclideanFlowBound (normalizedHamiltonian I hI) : ℝ) * t) -
          Real.exp ((euclideanFlowBound (normalizedHamiltonian I hI) : ℝ) * t)) ∧
      (‖fderiv ℝ (euclideanMap (Ψ (a + t) (-t))) x‖ ≤
        Real.exp ((euclideanFlowBound (normalizedHamiltonian I hI) : ℝ) * t) ∧
      ‖fderiv ℝ (fderiv ℝ (euclideanMap (Ψ (a + t) (-t)))) x‖ ≤
        Real.exp (2 * (euclideanFlowBound (normalizedHamiltonian I hI) : ℝ) * t) -
          Real.exp ((euclideanFlowBound (normalizedHamiltonian I hI) : ℝ) * t))) ∧
    (∀ x y, dist (euclideanMap (Ψ a t) x) (euclideanMap (Ψ a t) y) ≤
      Real.exp ((euclideanFlowBound (normalizedHamiltonian I hI) : ℝ) * t) * dist x y) := by
  let L : ℝ := euclideanFlowBound (normalizedHamiltonian I hI)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hB₁ : 1 ≤ Real.exp (L * t) := Real.one_le_exp (mul_nonneg hL ht)
  have hB₂ : 0 ≤ Real.exp (2 * L * t) - Real.exp (L * t) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    nlinarith
  have hb := (planar_euclidean_flow_estimates (normalizedHamiltonian_valid I hI)
    (normalizedHamiltonian_noTime I hI) hv).2.2 a t ht
  have hf := compactTransition_euclidean_transfer I hI hΨ hΩ a t hB₁ hB₂ (fun x => (hb.1 x).1)
  have hi := compactTransition_euclidean_transfer I hI hΨ hΩ (a + t) (-t) hB₁ hB₂ (fun x => (hb.1 x).2)
  refine ⟨fun x => ⟨hf x, hi x⟩, ?_⟩
  intro x y
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := (univ : Set EuclideanPlane))
    (fun z _ => (compactTransition_euclidean_smooth I hI hΨ hΩ hv a t).differentiable (by simp) z)
    (fun z _ => (hf z).1) (convex_univ : Convex ℝ (univ : Set EuclideanPlane))
    (mem_univ y) (mem_univ x)
  simpa only [dist_eq_norm] using h

end Recorder.Planar
end ForcedComputation

end

end OAI
