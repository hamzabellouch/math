import OAI.Analysis.NuclearUltrapower.GroupObstruction
import OAI.Analysis.NuclearUltrapower.Kazhdan
import OAI.Analysis.NuclearUltrapower.Model

namespace OAI

section
noncomputable section
universe u v w
namespace NuclearUltrapower
/-- Exact main obligation, using an existential representative of the universal
C*-algebra. Proving this includes existence of C*(G), not just an implication
from an assumed universal model, and includes its separability.
The nonembedding assertion has no separability restriction on B. -/
def MainStatement : Prop :=
  ∃ (A : UnitalCStar.{u}) (ι : G →* unitary A),
    IsFullGroupAlgebra A ι ∧ TopologicalSpace.SeparableSpace A ∧
    ∀ (B : UnitalCStar.{u}), IsNuclear.{u, u} B →
      ∀ (ω : Ultrafilter ℕ), IsFree ω →
        ¬ ∃ φ : A →⋆ₐ[ℂ] NormUltrapower B ω, Function.Injective φ

end NuclearUltrapower
end
end

section

noncomputable section
namespace NuclearUltrapower

instance : Countable Dyadic :=
  (IsLocalization.mk'_surjective (Submonoid.powers (2 : ℤ)) (S := Dyadic)).countable

instance : Countable SL3Z := by
  unfold SL3Z Matrix.SpecialLinearGroup Matrix
  infer_instance

instance : Countable Vector3 := by
  unfold Vector3
  infer_instance

instance : Countable G := by
  have : Countable (Multiplicative Vector3) := inferInstanceAs (Countable Vector3)
  have : Countable (Multiplicative ℤ) := inferInstanceAs (Countable ℤ)
  exact SemidirectProduct.equivProd.injective.countable

/-- The exact dyadic ambient group has a full group C*-algebra with the stated
universal property, separability, and obstruction for every nuclear target. -/
theorem main_statement : MainStatement.{0} := by
  let A : UnitalCStar := ⟨FullGroupModel.Full G⟩
  refine ⟨A, FullGroupModel.inclusion G, ?_, inferInstance, ?_⟩
  · refine ⟨FullGroupModel.dense_span G, ?_⟩
    intro D ρ
    refine ⟨FullGroupModel.modelMap G ρ, FullGroupModel.modelMap_generator G ρ, ?_⟩
    intro φ hφ
    exact FullGroupModel.modelMap_unique G ρ φ hφ
  · intro B hB ω hω
    obtain ⟨π,hπ,haπ⟩ := Elementary.exists_aperiodic_integral_rep
    apply fullGroup_no_nuclear_ultrapower Elementary.integralInclusion
      Elementary.integralInclusion_injective Elementary.integralTheta
      Elementary.integralTheta_injective Elementary.stableLetter ?_
      Elementary.kazhdanSet Elementary.kazhdanSet_nonempty Elementary.kazhdanSet_generates
      (1/4000) (by norm_num) ?_ Elementary.hasKazhdanGap π hπ haπ hB ω hω
    · intro g
      have h := Elementary.stableLetter_conjugation g
      calc
        _ = (Elementary.stableLetter * Elementary.integralInclusion g *
          Elementary.stableLetter⁻¹) * Elementary.stableLetter := congrArg (· * _) h.symm
        _ = _ := by group
    · have hc : 1 ≤ (Elementary.kazhdanSet.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr Elementary.kazhdanSet_nonempty
      linarith

end NuclearUltrapower
end
end

end OAI
