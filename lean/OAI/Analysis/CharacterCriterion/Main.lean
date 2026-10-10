import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.JiangSu

namespace OAI

noncomputable section

namespace KirchbergRordam

lemma nonzero_character_one {A : Type*} [CStarAlgebra A]
    (χ : A →⋆ₙₐ[ℂ] ℂ) (hχ : χ≠0) : χ 1=1 := by
  have hn : χ 1≠0 := by
    intro h
    apply hχ
    ext a
    change χ a=0
    calc
      χ a = χ (1*a) := by rw [one_mul]
      _ = χ 1*χ a := map_mul χ _ _
      _ = 0 := by rw [h,zero_mul]
  apply mul_left_cancel₀ hn
  rw [←map_mul χ,one_mul,mul_one]
def unitalCharacter {A : Type*} [CStarAlgebra A]
    (χ : A →⋆ₙₐ[ℂ] ℂ) (hχ : χ≠0) : A →⋆ₐ[ℂ] ℂ where
  toFun := χ
  map_zero' := map_zero χ
  map_one' := nonzero_character_one χ hχ
  map_add' := map_add χ
  map_mul' := map_mul χ
  commutes' z := by
    change χ (algebraMap ℂ A z)=z
    rw [Algebra.algebraMap_eq_smul_one,map_smul,nonzero_character_one χ hχ,
      smul_eq_mul,mul_one]
  map_star' := map_star χ


lemma hasNoCharacters_iff (A : Type*) [CStarAlgebra A] :
    HasNoCharacters A ↔ IsEmpty (A →⋆ₐ[ℂ] ℂ) := by
  classical
  constructor
  · intro h
    refine ⟨fun χ => ?_⟩
    have he := DFunLike.congr_fun (h χ.toNonUnitalStarAlgHom) 1
    change χ 1=0 at he
    rw [map_one] at he
    exact one_ne_zero he
  · intro h χ
    by_contra hn
    exact h.false (unitalCharacter χ hn)
attribute [local instance 1100] StarCompletion.completionStar

theorem character_criterion
    (A : Type) [CStarAlgebra A] [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.cofinite) :
    HasNoCharacters (NormUltrapower.CentralAlgebra A ω) ↔
      Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A JiangSu.Algebra) := by
  rw [hasNoCharacters_iff]
  exact StandardPrimeModel.presentation.character_criterion A ω hω
end KirchbergRordam
end

end OAI
