import OAI.Analysis.CircleDomains.Topology.JordanFillLimits

namespace OAI

/-!
# Interior stability of Jordan fills with an interior anchor

Uniformly converging Jordan contours retain every compact part of the
limiting interior if one convergent sequence of interior points is
known. A smaller connected Jordan disk joins that anchor to the compact
set, and avoids all approximating boundaries. This uses no winding-number
assumption.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_compact_subset_jordanInterior_of_anchor
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {z : ℂ} {zn : ℕ → ℂ} (hz : z ∈ jordanInterior H)
    (hzn : Tendsto zn atTop (𝓝 z))
    (hanchor : ∀ᶠ n in atTop, zn n ∈ jordanInterior (J n))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H) :
    ∀ᶠ n in atTop, K ⊆ jordanInterior (J n) := by
  let S := H.symm '' (K ∪ {z})
  have hS : IsCompact S := (hK.union isCompact_singleton).image H.symm.continuous
  have hSball : S ⊆ ball (0 : ℂ) 1 := by
    rintro x ⟨w, hw, rfl⟩
    have hwH : w ∈ jordanInterior H := hw.elim (fun h => hKH h) (fun h => mem_singleton_iff.mp h ▸ hz)
    obtain ⟨t, ht, rfl⟩ := hwH
    simpa only [H.symm_apply_apply] using ht
  obtain ⟨r, ⟨hr, hr1⟩, hSr⟩ := exists_pos_lt_subset_ball zero_lt_one hS.isClosed hSball
  let D := dilatedJordan H r hr
  let C := closure (jordanInterior D)
  have hD : jordanInterior D = H '' ball (0 : ℂ) r := jordanInterior_dilated H hr
  have hC : C = H '' closedBall (0 : ℂ) r := by
    dsimp only [C]
    rw [hD, ← H.image_closure, closure_ball 0 hr.ne']
  have hKC : K ⊆ C := by
    intro x hx
    apply subset_closure
    rw [hD]
    exact ⟨H.symm x, hSr ⟨x, Or.inl hx, rfl⟩, H.apply_symm_apply x⟩
  have hzD : z ∈ jordanInterior D := by
    rw [hD]
    exact ⟨H.symm z, hSr ⟨z, Or.inr rfl, rfl⟩, H.apply_symm_apply z⟩
  have hCH : C ⊆ jordanInterior H := by
    rw [hC]
    apply image_mono
    exact closedBall_subset_ball hr1
  have hCcompact : IsCompact C := isCompact_closure_jordanInterior D
  have hCconn : IsPreconnected C := (isConnected_jordanInterior D).isPreconnected.closure
  have hγC : range γ ⊆ Cᶜ := by
    rw [hfront]
    intro x hx hxC
    have hxH := hCH hxC
    have hnot : x ∉ jordanInterior H := by
      simpa only [(jordanInterior_isOpen H).interior_eq] using hx.2
    exact hnot hxH
  obtain ⟨δ, hδ, hδC⟩ := (isCompact_range hγ).exists_thickening_subset_open
    hCcompact.isClosed.isOpen_compl hγC
  have hclose := Metric.tendstoUniformly_iff.mp hlim δ hδ
  have hznD : ∀ᶠ n in atTop, zn n ∈ jordanInterior D :=
    hzn ((jordanInterior_isOpen D).mem_nhds hzD)
  filter_upwards [hclose, hfrontn, hznD, hanchor] with n hn hnfront hnD hnanchor
  have hnC : frontier (jordanInterior (J n)) ⊆ Cᶜ := by
    rw [← hnfront]
    rintro x ⟨t, rfl⟩
    apply hδC
    exact mem_thickening_iff.mpr ⟨γ t, mem_range_self t, by simpa only [dist_comm] using hn t⟩
  have hCJ : C ⊆ jordanInterior (J n) := by
    apply hCconn.subset_of_closure_inter_subset (jordanInterior_isOpen (J n))
      ⟨zn n, subset_closure hnD, hnanchor⟩
    rintro x ⟨hxcl, hxC⟩
    by_contra hxJ
    have hxf : x ∈ frontier (jordanInterior (J n)) := by
      rw [frontier, (jordanInterior_isOpen (J n)).interior_eq]
      exact ⟨hxcl, hxJ⟩
    exact hnC hxf hxC
  exact hKC.trans hCJ

end CircleDomainRigidity

end

end OAI
