import Mathlib
import OAI.Analysis.FreeWords.FiniteMomentNet
import OAI.Analysis.FreeWords.HaarEndpointLimits
import OAI.Analysis.FreeWords.HaarFiniteEndpointsDefinitions

namespace OAI

noncomputable section

namespace KKHaarEndpoints

noncomputable section

open Filter

open scoped Topology

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

theorem haar_finite_endpoints : HaarFiniteEndpoints (A := A) := by
  classical
  intro τ B Good h1 htr happ K F E hF hE ε hε
  let T := {k : ℤ // k≠0} ⊕ {w : List (ℤ×A) // w≠[] ∧ CenteredPowerWord τ B w}
  let f : T → unitary A → ℂ := fun t u => match t with
    | .inl k => τ (u^k.val).val
    | .inr w => τ (powerWord u w.val)
  have hfinite : ∀L:Finset T, ∀η:ℝ,0<η → ∃u,Good u ∧ ∀t∈L,‖f t u‖<η := by
    intro L η hη
    let K₀ : Finset ℤ := L.image (fun t => match t with | .inl k => k.val | .inr _ => 0)
    let F₀ : Finset (List (ℤ×A)) := L.biUnion (fun t => match t with | .inl _ => ∅ | .inr w => {w.val})
    have hF₀ : ∀w∈F₀,w≠[] ∧ CenteredPowerWord τ B w := by
      intro w hw
      obtain ⟨t,ht,hw⟩ := Finset.mem_biUnion.mp hw
      cases t with
      | inl k => simp at hw
      | inr v => have he := Finset.mem_singleton.mp hw; subst w; exact v.property
    obtain ⟨u,hgood,hK₀,hF₀'⟩ := happ K₀ F₀ hF₀ η hη
    refine ⟨u,hgood,?_⟩
    intro t ht
    cases t with
    | inl k => exact hK₀ k.val (Finset.mem_image.mpr ⟨.inl k,ht,rfl⟩) k.property
    | inr w => exact hF₀' w.val (Finset.mem_biUnion.mpr ⟨.inr w,ht,by simp⟩)
  obtain ⟨u,hgood,hu⟩ := KKFiniteMomentNet.finite_moment_net Good f hfinite
  have hH (k : ℤ) (hk : k≠0) : Tendsto (fun j => τ (u j^k).val) atTop (𝓝 0) := hu (.inl ⟨k,hk⟩)
  have hC (w : List (ℤ×A)) (hne : w≠[]) (hc : CenteredPowerWord τ B w) :
      Tendsto (fun j => τ (powerWord (u j) w)) atTop (𝓝 0) := hu (.inr ⟨w,hne,hc⟩)
  have hO := haar_endpoint_limits (A := A) (Finset T×ℕ) atTop τ B u h1 htr hH hC
  have hKsmall : ∀ᶠj in atTop,∀k∈K,k≠0 → ‖τ (u j^k).val‖<ε := by
    apply (Filter.eventually_all_finset K).2
    intro k hk
    by_cases hk0 : k=0
    · exact Eventually.of_forall (fun _ h => (h hk0).elim)
    · have hh := Metric.tendsto_nhds.mp (hH k hk0) ε hε
      simpa only [dist_zero_right] using hh.mono (fun j hj _ => hj)
  have hFsmall : ∀ᶠj in atTop,∀w∈F,‖τ (powerWord (u j) w)‖<ε := by
    apply (Filter.eventually_all_finset F).2
    intro w hw
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp (hC w (hF w hw).1 (hF w hw).2) ε hε
  have hEsmall : ∀ᶠj in atTop,∀z∈E,‖τ (powerWord (u j) z.1*(u j^z.2).val)‖<ε := by
    apply (Filter.eventually_all_finset E).2
    intro z hz
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp (hO z.1 (hE z hz).1 z.2 (hE z hz).2) ε hε
  obtain ⟨j,hjK,hjF,hjE⟩ := (hKsmall.and (hFsmall.and hEsmall)).exists
  exact ⟨u j,hgood j,hjK,hjF,hjE⟩

end

end KKHaarEndpoints
end

end OAI
