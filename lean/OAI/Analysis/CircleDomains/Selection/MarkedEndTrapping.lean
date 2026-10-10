import OAI.Analysis.CircleDomains.Topology.JordanFillLimits
import OAI.Analysis.CircleDomains.Topology.MarkedDiskLimits
import OAI.Analysis.CircleDomains.Transfer.SourceTargetEnds

namespace OAI

/-!
# Passing marked finite disks to their prescribed ends

The finite-stage geometric containment and uniform convergence on each
fixed boundary curve imply containment in the whole limiting end component.
No winding-number or boundary-extension hypothesis is used.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem limit_disk_subset_jordan_fill
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (htrap : ∀ᶠ n in atTop, closedBall (c n) (r n) ⊆ closure (jordanInterior (J n))) :
    closedBall c₀ r₀ ⊆ closure (jordanInterior H) := by
  intro z hz
  rw [closedBall_eq_affine_image hr₀ c₀] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  apply mem_jordan_fill_of_tendsto H J γ γn hγ hfront hfrontn hlim
    (hc.add (hrlim.smul_const u))
  filter_upwards [htrap] with n hn
  apply hn
  rw [closedBall_eq_affine_image (hr n) (c n)]
  exact mem_image_of_mem _ hu

theorem limit_disk_subset_prescribed_end
    (H : ℕ → ℂ ≃ₜ ℂ) (J : ℕ → ℕ → ℂ ≃ₜ ℂ)
    (γ : ℕ → Circle → ℂ) (γn : ℕ → ℕ → Circle → ℂ)
    (hγ : ∀ j, Continuous (γ j))
    (hfront : ∀ j, range (γ j) = frontier (jordanInterior (H j)))
    (hfrontn : ∀ j, ∀ᶠ n in atTop, range (γn j n) = frontier (jordanInterior (J j n)))
    (hlim : ∀ j, TendstoUniformly (γn j) (γ j) atTop)
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (htrap : ∀ j, ∀ᶠ n in atTop,
      closedBall (c n) (r n) ⊆ closure (jordanInterior (J j n))) :
    ((↑) : ℂ → Sphere) '' closedBall c₀ r₀ ⊆ ⋂ j, closedTerminalCap (H j) := by
  rintro _ ⟨z, hz, rfl⟩
  apply mem_iInter.mpr
  intro j
  exact ⟨z, limit_disk_subset_jordan_fill (H j) (J j) (γ j) (γn j)
    (hγ j) (hfront j) (hfrontn j) (hlim j) hr hr₀ hc hrlim (htrap j) hz, rfl⟩

end CircleDomainRigidity

end

end OAI
