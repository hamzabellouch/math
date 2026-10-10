import OAI.Analysis.CircleDomains.Topology.JordanDiskImages
import OAI.Analysis.CircleDomains.Topology.AnchoredJordanLimits

namespace OAI

/-! Compact subsets of an embedded source disk's limiting image remain in the actual images
under locally uniform convergence of the finite open embeddings. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_compact_subset_image_jordan_disk
    (hsch : PlanarSchoenflies)
    {G : Set ℂ} (hG : IsOpen G) {f : ℂ → ℂ} (hf : ContinuousOn f G)
    (hfo : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hfi : InjOn f G)
    (Gn : ℕ → Set ℂ) (hGn : ∀ n, IsOpen (Gn n)) (fn : ℕ → ℂ → ℂ)
    (hfn : ∀ n, ContinuousOn (fn n) (Gn n))
    (hfno : ∀ n S, IsOpen S → S ⊆ Gn n → IsOpen (fn n '' S))
    (hfni : ∀ n, InjOn (fn n) (Gn n))
    (hlim : TendstoLocallyUniformlyOn fn f atTop G)
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ G)
    (hretain : ∀ᶠ n in atTop, closure (jordanInterior H) ⊆ Gn n)
    {K : Set ℂ} (hK : IsCompact K) (hKf : K ⊆ f '' jordanInterior H) :
    ∀ᶠ n in atTop, K ⊆ fn n '' jordanInterior H := by
  classical
  obtain ⟨J, hJ, _, hJfront⟩ := exists_jordan_image_disk hsch hG hf hfo hfi H hHG
  have hex (n : ℕ) : ∃ Jn : ℂ ≃ₜ ℂ, closure (jordanInterior H) ⊆ Gn n →
      fn n '' jordanInterior H = jordanInterior Jn ∧
      frontier (jordanInterior Jn) = fn n '' frontier (jordanInterior H) := by
    by_cases hn : closure (jordanInterior H) ⊆ Gn n
    · obtain ⟨Jn, hJn, _, hJnf⟩ :=
        exists_jordan_image_disk hsch (hGn n) (hfn n) (hfno n) (hfni n) H hn
      exact ⟨Jn, fun _ => ⟨hJn, hJnf⟩⟩
    · exact ⟨J, fun h => (hn h).elim⟩
  choose Jn hJn using hex
  let γ : Circle → ℂ := fun t => f (H t)
  let γn : ℕ → Circle → ℂ := fun n t => fn n (H t)
  have hcircle (t : Circle) : H (t : ℂ) ∈ G := by
    apply hHG
    rw [closure_jordanInterior]
    exact ⟨t, by simp, rfl⟩
  have hcurve : Continuous (fun t : Circle => H (t : ℂ)) :=
    H.continuous.comp continuous_subtype_val
  have hγ : Continuous γ := hf.comp_continuous hcurve hcircle
  have hrange : range (fun t : Circle => H (t : ℂ)) = frontier (jordanInterior H) := by
    rw [frontier_jordanInterior]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hγfront : range γ = frontier (jordanInterior J) := by
    rw [hJfront, ← hrange, ← range_comp]
    rfl
  have hγnfront : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (Jn n)) := by
    filter_upwards [hretain] with n hn
    rw [(hJn n hn).2, ← hrange, ← range_comp]
    rfl
  have hγlim : TendstoUniformly γn γ atTop := by
    apply tendstoUniformlyOn_univ.mp
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_univ).mp
    exact hlim.comp (fun t : Circle => H (t : ℂ)) (fun t _ => hcircle t) hcurve.continuousOn
  have hxH : H 0 ∈ jordanInterior H := ⟨0, by simp, rfl⟩
  have hxG := hHG (subset_closure hxH)
  have hxJ : f (H 0) ∈ jordanInterior J := hJ ▸ mem_image_of_mem f hxH
  have hxJn : ∀ᶠ n in atTop, fn n (H 0) ∈ jordanInterior (Jn n) := by
    filter_upwards [hretain] with n hn
    rw [← (hJn n hn).1]
    exact mem_image_of_mem _ hxH
  have hp := eventually_compact_subset_jordanInterior_of_anchor J Jn γ γn
    hγ hγfront hγnfront hγlim hxJ (hlim.tendsto_at hxG) hxJn hK (hJ ▸ hKf)
  filter_upwards [hp, hretain] with n hn hr
  rwa [← (hJn n hr).1] at hn

end CircleDomainRigidity

end

end OAI
