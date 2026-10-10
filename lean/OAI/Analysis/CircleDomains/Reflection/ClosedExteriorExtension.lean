import OAI.Analysis.CircleDomains.Reflection.ClosedExteriorCorrespondence

namespace OAI

/-! The canonical unnormalized extension and its exact compact image. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma analytic_closed_exterior_extension {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    let U := (closedTerminalCap H)ᶜ
    let V := (((↑) : ℂ → Sphere) '' closedBall d s)ᶜ
    let T := exteriorDiskNormalization d s hs
    let E := T.symm ∘ extendFrom U (T ∘ f)
    ContinuousOn E (closure U) ∧ EqOn E f U ∧ InjOn E (closure U) ∧
      E '' closure U=closure V := by
  dsimp only
  let U := (closedTerminalCap H)ᶜ
  let V := (((↑) : ℂ → Sphere) '' closedBall d s)ᶜ
  let T := exteriorDiskNormalization d s hs
  let E := extendFrom U (T ∘ f)
  obtain ⟨hc,he⟩ := analytic_sphere_closed_exterior_extension hH hs hf
  change ContinuousOn E (closure U) at hc
  change EqOn E (T ∘ f) U at he
  refine ⟨T.symm.continuous.comp_continuousOn hc,?_,
    T.symm.injective.comp_injOn (analytic_sphere_closed_exterior_injective hH hs hf),?_⟩
  · intro p hp
    change T.symm (E p)=f p
    rw [he hp]
    exact T.symm_apply_apply _
  · rw [image_comp,analytic_sphere_closed_exterior_image hH hs hf]
    have hcl := exteriorDiskNormalization_image_closure d hs
    rw [←hcl,image_image]
    simp only [Homeomorph.symm_apply_apply,image_id']

lemma closed_extension_image_of_compact {X Y:Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {A:Set X} {f g:X→Y} (hc:IsCompact (closure A))
    (hf:ContinuousOn f (closure A)) (he:EqOn f g A) :
    f '' closure A=closure (g '' A) := by
  rw [←image_congr he]
  apply Subset.antisymm hf.image_closure
  exact closure_minimal (image_mono subset_closure) (hc.image_of_continuousOn hf).isClosed

end CircleDomainRigidity

end

end OAI
