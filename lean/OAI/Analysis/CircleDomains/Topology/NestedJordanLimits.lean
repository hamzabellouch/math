import OAI.Analysis.CircleDomains.Topology.AnchoredJordanLimits

namespace OAI

/-!
# Strict nesting survives anchored Jordan limits

An intermediate compact Jordan disk separates the limiting contours.
Upper containment retains the inner approximations in that disk; the
interior-anchor lemma retains that disk inside the outer approximations.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_nested_jordanInteriors_of_anchor
    (H K : ℂ ≃ₜ ℂ) (Hn Kn : ℕ → ℂ ≃ₜ ℂ)
    (γ δ : Circle → ℂ) (γn δn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hδ : Continuous δ)
    (hγfront : range γ = frontier (jordanInterior H))
    (hδfront : range δ = frontier (jordanInterior K))
    (hγn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (Hn n)))
    (hδn : ∀ᶠ n in atTop, range (δn n) = frontier (jordanInterior (Kn n)))
    (hγlim : TendstoUniformly γn γ atTop) (hδlim : TendstoUniformly δn δ atTop)
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {z : ℂ} {zn : ℕ → ℂ} (hz : z ∈ jordanInterior K)
    (hzn : Tendsto zn atTop (𝓝 z))
    (hanchor : ∀ᶠ n in atTop, zn n ∈ jordanInterior (Kn n)) :
    ∀ᶠ n in atTop, closure (jordanInterior (Hn n)) ⊆ jordanInterior (Kn n) := by
  obtain ⟨r, hr, hrsub, _⟩ := exists_disjoint_jordan_enlargements (fun _ : Unit => H)
    (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    (fun _ => jordanInterior K) (fun _ => jordanInterior_isOpen K) (fun _ => hHK)
  let r₀ := r Unit.unit
  let C := H '' closedBall (0 : ℂ) r₀
  let O := H '' ball (0 : ℂ) r₀
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) r₀).image H.continuous
  have hO : IsOpen O := H.isOpenMap _ isOpen_ball
  have hCO : O ⊆ C := image_mono ball_subset_closedBall
  have hHC : closure (jordanInterior H) ⊆ O := by
    rw [closure_jordanInterior]
    exact image_mono (closedBall_subset_ball (hr Unit.unit))
  have hCK : C ⊆ jordanInterior K := hrsub Unit.unit
  have hinner := eventually_jordan_fill_subset_open H Hn γ γn hγ hγfront hγn hγlim hO hHC
  have houter := eventually_compact_subset_jordanInterior_of_anchor K Kn δ δn hδ hδfront
    hδn hδlim hz hzn hanchor hC hCK
  filter_upwards [hinner, houter] with n hn hn'
  exact hn.trans (hCO.trans hn')

end CircleDomainRigidity

end

end OAI
