import OAI.Analysis.CircleDomains.Topology.JordanDiskImages
import OAI.Analysis.CircleDomains.Topology.JordanFillLimits

namespace OAI

/-! A target-domain point has a compact source Jordan anchor whose image contains a target ball
inside any prescribed open neighborhood. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def roundJordanAt (c : ℂ) (r : ℝ) (hr : 0 < r) : ℂ ≃ₜ ℂ :=
  dilatedJordan (Homeomorph.addRight c) r hr

theorem roundJordanAt_interior (c : ℂ) (r : ℝ) (hr : 0 < r) :
    jordanInterior (roundJordanAt c r hr) = ball c r := by
  rw [roundJordanAt, jordanInterior_dilated _ hr]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ball, dist_eq_norm]
    change ‖(w + c) - c‖ < r
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw
  · intro hz
    refine ⟨z - c, ?_, ?_⟩
    · simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
    · simp

theorem roundJordanAt_closure (c : ℂ) (r : ℝ) (hr : 0 < r) :
    closure (jordanInterior (roundJordanAt c r hr)) = closedBall c r := by
  rw [roundJordanAt_interior, closure_ball _ hr.ne']

theorem exists_source_jordan_anchor {f : ℂ → ℂ} {G W : Set ℂ}
    (hG : IsOpen G) (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hW : IsOpen W) {a : ℂ} (ha : a ∈ f '' G) (haW : a ∈ W) :
    ∃ (H : ℂ ≃ₜ ℂ) (δ : ℝ), 0 < δ ∧
      closure (jordanInterior H) ⊆ G ∧ closedBall a δ ⊆ f '' jordanInterior H ∩ W := by
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨r, hr, hrG⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hG.mem_nhds hp)
  let H := roundJordanAt p r hr
  have hHG : closure (jordanInterior H) ⊆ G := by
    dsimp only [H]
    rw [roundJordanAt_closure]
    exact hrG
  have hpH : p ∈ jordanInterior H := by
    dsimp only [H]
    rw [roundJordanAt_interior]
    simpa only [mem_ball, dist_self] using hr
  have hopen : IsOpen (f '' jordanInterior H ∩ W) :=
    (ho _ (jordanInterior_isOpen H) (subset_closure.trans hHG)).inter hW
  obtain ⟨δ, hδ, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hopen.mem_nhds ⟨mem_image_of_mem _ hpH, haW⟩)
  exact ⟨H, δ, hδ, hHG, hδsub⟩

end CircleDomainRigidity

end

end OAI
