import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FinitelyManyTranslationRelations

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteAlignedConfiguration

variable {α β G : Type*} [Group G] [Finite β] (f : α → G)

theorem finite_table_subgroup_inputs_eventually (L : ℕ)
    (K : Subgroup (BoundedRelationCover L f)) {T : Type*} [Group T] [Finite T]
    (φ : T →* G) (hφ : ∀ s, φ s ∈ K.map (coverMap L f))
    (input : β → T) (v : β → FreeGroup α)
    (hv : ∀ b, FreeGroup.lift f (v b) = φ (input b)) :
    ∃ B : ℕ, ∃ hLB : L ≤ B, ∀ M : ℕ, ∀ hBM : B ≤ M,
      ∃ ρ : T →* BoundedRelationCover M f,
        (coverMap M f).comp ρ = φ ∧
        ρ.range ≤ K.map (coverTransition f (le_trans hLB hBM)) ∧
        ∀ b, ρ (input b) = PresentedGroup.mk (shortRelations M f) (v b) := by
  choose y hy hyq using hφ
  choose w hw using fun s => PresentedGroup.mk_surjective (shortRelations L f) (y s)
  have hwp : ∀ s, FreeGroup.lift f (w s) = φ s := by
    intro s
    rw [← coverMap_mk L f,hw s,hyq s]
  obtain ⟨B₁,hB₁⟩ := finite_table_lift_eventually f φ w hwp
  obtain ⟨B₂,hB₂⟩ := finite_word_equalities_eventually f (fun b => w (input b)) v
    (fun b => (hwp (input b)).trans (hv b).symm)
  refine ⟨L+B₁+B₂,by omega,fun M hM => ?_⟩
  obtain ⟨ρ,hρ,hρw⟩ := hB₁ M (by omega)
  refine ⟨ρ,hρ,?_,?_⟩
  · rintro z ⟨s,rfl⟩
    refine ⟨y s,hy s,?_⟩
    rw [← hw s,coverTransition_mk,hρw s]
  · intro b
    rw [hρw]
    exact hB₂ M (by omega) b

end FiniteAlignedConfiguration

end SimpleAmenable
end
end

end OAI
