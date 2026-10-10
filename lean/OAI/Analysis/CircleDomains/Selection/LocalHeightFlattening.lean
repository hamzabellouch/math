import OAI.Analysis.CircleDomains.Selection.ControlledHeight
import OAI.Analysis.CircleDomains.Sobolev.CountableValueFlattening

namespace OAI

/-! The actual height admits simultaneous uniform and local energy
flattening at the countably many selected end values. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem ControlledHeight.exists_local_value_flattening
    (hcoarea : PlanarSobolevCoarea) {R d : ℝ} (H : ControlledHeight R d)
    (A : ℝ) {C : Set ℝ} (hC : C.Countable)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    let W := heightLimitWitness H.error₀ H.error₁
      (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient A
    ∃ O : Set ℝ, ∃ W' : DeGiorgi.MemW1pWitness 2
      (flattenValues O ∘ H.height ∘ complexPlaneCoordinates) (ball 0 A),
      IsOpen O ∧ C ⊆ O ∧ LipschitzWith 1 (flattenValues O) ∧
      (∀ t, |flattenValues O t-t| < δ) ∧
      (∫⁻ p in ball 0 A, ENNReal.ofReal (‖W'.weakGrad p-W.weakGrad p‖^2)) < ENNReal.ofReal ε ∧
      (∀ c ∈ C, ∃ V ∈ 𝓝 c, EqOn (flattenValues O) (fun _ => flattenValues O c) V) ∧
      (∀ p, W.weakGrad p = 0 → W'.weakGrad p = 0) := by
  have hv := H.height.continuous.comp complexPlaneCoordinates.continuous
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanPlane) A).bddAbove_image hv.norm.continuousOn
  apply exists_countable_value_flattening hcoarea isOpen_ball hv
    (heightLimitWitness H.error₀ H.error₁ hv H.weak_gradient A)
    (le_max_right B 0) ?_ hC hδ hε
  intro p hp
  apply abs_le.mp
  have hh : ‖H.height (complexPlaneCoordinates p)‖ ≤ B :=
    hB ⟨p, ball_subset_closedBall hp, rfl⟩
  exact (show |H.height (complexPlaneCoordinates p)| ≤ B from hh).trans (le_max_left _ _)

end CircleDomainRigidity

end

end OAI
