import OAI.Analysis.CircleDomains.Reflection.SphereClosedExteriorHomeomorph

namespace OAI

/-! The actual, unnormalized boundary correspondence on both compact
closed exteriors. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exteriorDiskNormalization_image_closure (d:ℂ) {s:ℝ} (hs:0<s) :
    exteriorDiskNormalization d s hs '' closure ((((↑):ℂ→Sphere) '' closedBall d s)ᶜ)=
      ((↑):ℂ→Sphere) '' closedBall 0 1 := by
  rw [(exteriorDiskNormalization d s hs).image_closure,
    exteriorDiskNormalization_image d hs]
  have hc := closure_sphere_image_jordanInterior (roundJordanAt (0:ℂ) 1 zero_lt_one)
  rwa [roundJordanAt_interior,closure_ball (0:ℂ) one_ne_zero] at hc

lemma exists_closed_exterior_correspondence {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    ∃e : closure (closedTerminalCap H)ᶜ ≃ₜ
        closure ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ),
      ∀p : closure (closedTerminalCap H)ᶜ, (p:Sphere)∈(closedTerminalCap H)ᶜ → (e p : Sphere)=f p := by
  obtain ⟨e,he⟩ := exists_sphere_closed_exterior_homeomorph hH hs hf
  let T := exteriorDiskNormalization d s hs
  let D := ((↑):ℂ→Sphere) '' closedBall 0 1
  let V := (((↑):ℂ→Sphere) '' closedBall d s)ᶜ
  have hcl : T.symm '' D=closure V := by
    change T.symm '' (((↑):ℂ→Sphere) '' closedBall 0 1)=closure V
    rw [←exteriorDiskNormalization_image_closure d hs,image_image]
    simp only [T,Homeomorph.symm_apply_apply,image_id']
    rfl
  let k : D ≃ₜ closure V := (T.symm.image D).trans (Homeomorph.setCongr hcl)
  refine ⟨e.trans k,?_⟩
  intro p hp
  change T.symm (e p : Sphere)=f p
  rw [he]
  have hEe := (analytic_sphere_closed_exterior_extension hH hs hf).2
  rw [hEe hp]
  exact T.symm_apply_apply _

end CircleDomainRigidity

end

end OAI
