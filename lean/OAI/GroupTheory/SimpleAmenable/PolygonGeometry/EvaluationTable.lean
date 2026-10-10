import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.Sectors

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section EvaluationTable
variable {D H Q T : Type*} [Group D] [Group H] [Group Q] [Group T]

noncomputable def evaluationModel (q : H →* Q) (e : D →* H)
    (v : D →* T) (ρ : T →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) : e.range →* T :=
  e.rangeRestrict.liftOfSurjective e.rangeRestrict_surjective
    ⟨v,by
      intro w hw
      apply hρ
      have hh := DFunLike.congr_fun he w
      change q (e w) = ρ (v w) at hh
      have hw' : e w = 1 := congrArg Subtype.val hw
      rw [hw',map_one] at hh
      simpa only [map_one] using hh.symm⟩

theorem evaluationModel_comp (q : H →* Q) (e : D →* H)
    (v : D →* T) (ρ : T →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) :
    (evaluationModel q e v ρ hρ he).comp e.rangeRestrict = v :=
  e.rangeRestrict.liftOfRightInverse_comp _ _ _

theorem evaluationModel_projection (q : H →* Q) (e : D →* H)
    (v : D →* T) (ρ : T →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) :
    q.comp e.range.subtype = ρ.comp (evaluationModel q e v ρ hρ he) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨w,rfl⟩ := e.rangeRestrict_surjective x
  have hh := DFunLike.congr_fun (evaluationModel_comp q e v ρ hρ he) w
  change evaluationModel q e v ρ hρ he (e.rangeRestrict w) = v w at hh
  simp only [MonoidHom.comp_apply,hh]
  exact DFunLike.congr_fun he w

noncomputable def evaluationTable {Ω E : Type*} [Group E]
    (q : H →* Q) (e : D →* H) (v : D →* (Ω → E))
    (ρ : (Ω → E) →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) (hv : Function.Surjective v)
    (h : CentralOn q e.range) : ActualLawfulTable q ρ where
  carrier := e.range
  law := h
  model := evaluationModel q e v ρ hρ he
  onto := by
    intro s
    obtain ⟨w,rfl⟩ := hv s
    exact ⟨e.rangeRestrict w,DFunLike.congr_fun (evaluationModel_comp q e v ρ hρ he) w⟩
  projection := evaluationModel_projection q e v ρ hρ he

end EvaluationTable

end SimpleAmenable
end
end

end OAI
