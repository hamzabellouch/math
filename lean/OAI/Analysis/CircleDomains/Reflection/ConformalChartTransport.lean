import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanParametrization

namespace OAI

/-! An injective holomorphic continuation in a source chart transfers
back to an open neighborhood in the actual source plane. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma transport_injective_holomorphic_chart {N V : Set ℂ} {κ F : ℂ → ℂ}
    (hN : IsOpen N) (hV : IsOpen V) (h0N : (0:ℂ)∈N) (h0V : (0:ℂ)∈V)
    (hκ : DifferentiableOn ℂ κ N) (hi : InjOn κ N)
    (hF : DifferentiableOn ℂ F V) (hFi : InjOn F V) :
    ∃ (W : Set ℂ) (G : ℂ → ℂ), IsOpen W ∧ κ 0∈W ∧
      W=κ '' (N∩V) ∧ DifferentiableOn ℂ G W ∧ InjOn G W ∧
      ∀z∈N∩V,G (κ z)=F z := by
  let W := κ '' (N∩V)
  let G : ℂ → ℂ := F ∘ invFunOn κ N
  have hW : IsOpen W := holomorphic_injOn_isOpen_image hN hκ hi (hN.inter hV) inter_subset_left
  have hleft : ∀z∈N,G (κ z)=F z := by
    intro z hz
    change F (invFunOn κ N (κ z))=F z
    rw [hi.leftInvOn_invFunOn hz]
  refine ⟨W,G,hW,⟨0,⟨h0N,h0V⟩,rfl⟩,rfl,?_,?_,fun z hz => hleft z hz.1⟩
  · rintro x ⟨z,hz,rfl⟩
    have hFd : DifferentiableAt ℂ F (invFunOn κ N (κ z)) := by
      rw [hi.leftInvOn_invFunOn hz.1]
      exact (hF z hz.2).differentiableAt (hV.mem_nhds hz.2)
    have hd := hFd.comp (κ z)
      (holomorphicInjOn_inverse_differentiableAt hN hκ hi hz.1)
    exact hd.differentiableWithinAt
  · rintro x ⟨z,hz,rfl⟩ y ⟨w,hw,rfl⟩ he
    rw [hleft z hz.1,hleft w hw.1] at he
    exact congrArg κ (hFi hz.2 hw.2 he)

end CircleDomainRigidity

end

end OAI
