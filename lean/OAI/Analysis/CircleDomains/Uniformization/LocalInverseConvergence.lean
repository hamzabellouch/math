import OAI.Analysis.CircleDomains.Topology.CompactImageRetention
import OAI.Analysis.CircleDomains.Transfer.SourceAnchor

namespace OAI

/-! Locally uniform open embeddings have pointwise convergent actual
inverses on the limiting image. The small source disks are constructed. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem inverse_tendsto_of_locally_uniform_open_embeddings
    (hsch : PlanarSchoenflies)
    {G : Set ℂ} (hG : IsOpen G) {f : ℂ → ℂ} (hf : ContinuousOn f G)
    (hfo : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hfi : InjOn f G)
    (Gn : ℕ → Set ℂ) (hGn : ∀ n, IsOpen (Gn n)) (fn gn : ℕ → ℂ → ℂ)
    (hfn : ∀ n, ContinuousOn (fn n) (Gn n))
    (hfno : ∀ n S, IsOpen S → S ⊆ Gn n → IsOpen (fn n '' S))
    (hfni : ∀ n, InjOn (fn n) (Gn n))
    (hleft : ∀ n x, x ∈ Gn n → gn n (fn n x) = x)
    (hlim : TendstoLocallyUniformlyOn fn f atTop G)
    (hretain : ∀ K : Set ℂ, IsCompact K → K ⊆ G → ∀ᶠ n in atTop, K ⊆ Gn n)
    {x : ℂ} (hx : x ∈ G) : Tendsto (fun n => gn n (f x)) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨r, hr, hrG⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hG.mem_nhds hx)
  let δ := min r (ε / 2)
  have hδ : 0 < δ := lt_min hr (by positivity)
  have hδr : δ ≤ r := min_le_left _ _
  have hδε : δ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let H := roundJordanAt x δ hδ
  have hHG : closure (jordanInterior H) ⊆ G := by
    rw [show H = roundJordanAt x δ hδ from rfl, roundJordanAt_closure]
    exact (closedBall_subset_closedBall hδr).trans hrG
  have hxH : x ∈ jordanInterior H := by
    rw [show H = roundJordanAt x δ hδ from rfl, roundJordanAt_interior]
    exact mem_ball_self hδ
  have hsub := eventually_compact_subset_image_jordan_disk hsch hG hf hfo hfi Gn hGn fn
    hfn hfno hfni hlim H hHG
    (hretain _ (isCompact_closure_jordanInterior H) hHG) isCompact_singleton
    (singleton_subset_iff.mpr (mem_image_of_mem f hxH))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsub.and (hretain _ (isCompact_closure_jordanInterior H) hHG))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz, he⟩ := (hN n hn).1 (mem_singleton (f x))
  have hzG := (hN n hn).2 (subset_closure hz)
  rw [← he, hleft n z hzG]
  have hzδ : dist z x < δ := by
    simpa only [H, roundJordanAt_interior, mem_ball] using hz
  exact hzδ.trans hδε

end CircleDomainRigidity

end

end OAI
