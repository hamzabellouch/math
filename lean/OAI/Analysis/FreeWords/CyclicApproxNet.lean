import Mathlib
import OAI.Analysis.FreeWords.FiniteMomentNet
import OAI.Analysis.FreeWords.HaarFiniteEndpointsDefinitions

namespace OAI

noncomputable section

namespace KKHaarEndpoints

noncomputable section

open Filter

open scoped Topology

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

abbrev CyclicTest (τ : A →ₗ[ℂ] ℂ) (B : Subalgebra ℂ A) :=
  {k : ℤ // k≠0} ⊕ {w : List (ℤ×A) // w≠[] ∧ CenteredPowerWord τ B w}

abbrev CyclicIndex (τ : A →ₗ[ℂ] ℂ) (B : Subalgebra ℂ A) := Finset (CyclicTest τ B)×ℕ

theorem cyclic_approx_net (τ : A →ₗ[ℂ] ℂ) (B : Subalgebra ℂ A) (Good : unitary A → Prop)
    (happ : FiniteCyclicApprox τ B Good) :
    ∃u:CyclicIndex τ B → unitary A, (∀j,Good (u j)) ∧
      (∀k:ℤ,k≠0 → Tendsto (fun j => τ (u j^k).val) atTop (𝓝 0)) ∧
      (∀w:List (ℤ×A),w≠[] → CenteredPowerWord τ B w →
        Tendsto (fun j => τ (powerWord (u j) w)) atTop (𝓝 0)) := by
  classical
  let T := CyclicTest τ B
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
  exact ⟨u,hgood,hH,hC⟩

end

end KKHaarEndpoints
end

end OAI
