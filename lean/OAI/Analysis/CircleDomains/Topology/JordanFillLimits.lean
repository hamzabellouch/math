import OAI.Analysis.CircleDomains.Topology.JordanExteriors
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-!
# Upper containment for limits of Jordan fills

Uniform convergence of boundary parametrizations traps the approximating
closed fills in every neighborhood of the limiting closed fill. The proof
uses Jordan nesting and radial enlargement.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def dilatedJordan (H : ℂ ≃ₜ ℂ) (r : ℝ) (hr : 0 < r) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast hr.ne')).trans H

theorem jordanInterior_dilated (H : ℂ ≃ₜ ℂ) {r : ℝ} (hr : 0 < r) :
    jordanInterior (dilatedJordan H r hr) = H '' ball (0 : ℂ) r := by
  change (fun z : ℂ => H ((r : ℂ) * z)) '' ball 0 1 = H '' ball 0 r
  rw [← image_image]
  congr 1
  change (fun z : ℂ => r • z) '' ball 0 1 = ball 0 r
  exact smul_unitBall_of_pos (E := ℂ) hr

theorem eventually_jordan_fill_subset_open
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {O : Set ℂ} (hO : IsOpen O) (hHO : closure (jordanInterior H) ⊆ O) :
    ∀ᶠ n in atTop, closure (jordanInterior (J n)) ⊆ O := by
  obtain ⟨r, hr, hrO, _⟩ := exists_disjoint_jordan_enlargements
    (fun _ : Unit => H) (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    (fun _ => O) (fun _ => hO) (fun _ => hHO)
  let K := dilatedJordan H (r Unit.unit) (by linarith [hr Unit.unit])
  have hK : jordanInterior K = H '' ball (0 : ℂ) (r Unit.unit) :=
    jordanInterior_dilated H _
  have hγK : range γ ⊆ jordanInterior K := by
    rw [hfront, frontier_jordanInterior, hK]
    apply image_mono
    intro z hz
    simpa only [mem_ball, mem_sphere, dist_zero_right] using
      (show ‖z‖ < r Unit.unit by
        have hz' : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
        linarith [hr Unit.unit])
  obtain ⟨δ, hδ, hδK⟩ := (isCompact_range hγ).exists_thickening_subset_open
    (jordanInterior_isOpen K) hγK
  have hclose := Metric.tendstoUniformly_iff.mp hlim δ hδ
  filter_upwards [hclose, hfrontn] with n hn hnfront
  apply (closed_jordanInterior_subset_of_frontier_subset (J n) K ?_).trans
    (show jordanInterior K ⊆ O by
      rw [hK]
      exact (image_mono ball_subset_closedBall).trans (hrO Unit.unit))
  rw [← hnfront]
  rintro _ ⟨t, rfl⟩
  apply hδK
  apply mem_thickening_iff.mpr
  exact ⟨γ t, mem_range_self t, by simpa only [dist_comm] using hn t⟩

theorem mem_jordan_fill_of_tendsto
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {z : ℂ} {zn : ℕ → ℂ} (hz : Tendsto zn atTop (𝓝 z))
    (hzn : ∀ᶠ n in atTop, zn n ∈ closure (jordanInterior (J n))) :
    z ∈ closure (jordanInterior H) := by
  by_contra hnot
  have hnorm : 1 < ‖H.symm z‖ := by
    have hn : H.symm z ∉ closedBall (0 : ℂ) 1 := by
      intro h
      apply hnot
      rw [closure_jordanInterior]
      exact ⟨H.symm z, h, H.apply_symm_apply z⟩
    simpa only [mem_closedBall, dist_zero_right, not_le] using hn
  obtain ⟨r, hr, hrz⟩ := exists_between hnorm
  let K := dilatedJordan H r (by linarith)
  have hK : jordanInterior K = H '' ball (0 : ℂ) r := jordanInterior_dilated H _
  have hHK : closure (jordanInterior H) ⊆ jordanInterior K := by
    rw [closure_jordanInterior, hK]
    exact image_mono (closedBall_subset_ball hr)
  have hevent := eventually_jordan_fill_subset_open H J γ γn hγ hfront hfrontn hlim
    (jordanInterior_isOpen K) hHK
  have hzK : z ∈ closure (jordanInterior K) :=
    isClosed_closure.mem_of_tendsto hz (by
      filter_upwards [hevent, hzn] with n hn hnz
      exact subset_closure (hn hnz))
  rw [hK, ← H.image_closure, closure_ball 0 (by linarith : r ≠ 0)] at hzK
  obtain ⟨w, hw, hwz⟩ := hzK
  have hw' : w = H.symm z := H.injective (hwz.trans (H.apply_symm_apply z).symm)
  have hwle : ‖H.symm z‖ ≤ r := by simpa only [hw', mem_closedBall, dist_zero_right] using hw
  exact (not_le_of_gt hrz) hwle

end CircleDomainRigidity

end

end OAI
