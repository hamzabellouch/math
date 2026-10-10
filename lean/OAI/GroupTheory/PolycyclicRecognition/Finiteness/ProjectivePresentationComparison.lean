import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedStableSyzygyMap

namespace OAI

/-! # Comparing a projective presentation with the normalized free cover

The two kernel maps are inverse modulo maps through the projective middle
terms. No splitting of the original presentation is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem projectivePresentation_stable_comparison
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) [Projective S.X₂] :
    ∃ (a : normalizedSyzygy S.X₃ ⟶ S.X₁) (b : S.X₁ ⟶ normalizedSyzygy S.X₃),
      stableRepresentationClass _ _ (a ≫ b) = stableRepresentationClass _ _ (𝟙 _) ∧
      stableRepresentationClass _ _ (b ≫ a) = stableRepresentationClass _ _ (𝟙 _) := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let F := normalizedFreeRepresentation S.X₃
  let ε := normalizedFreeAugmentation S.X₃
  let l : F ⟶ S.X₂ := Projective.factorThru ε S.g
  have hl : l ≫ S.g = ε := Projective.factorThru_comp _ _
  let r : S.X₂ ⟶ F := Projective.factorThru S.g ε
  have hr : r ≫ ε = S.g := Projective.factorThru_comp _ _
  have hal : (kernel.ι ε ≫ l) ≫ S.g = 0 := by
    rw [Category.assoc, hl, kernel.condition]
  let a : normalizedSyzygy S.X₃ ⟶ S.X₁ := hS.exact.lift (kernel.ι ε ≫ l) hal
  have ha : a ≫ S.f = kernel.ι ε ≫ l := hS.exact.lift_f _ _
  have hbr : (S.f ≫ r) ≫ ε = 0 := by rw [Category.assoc, hr, S.zero]
  let b : S.X₁ ⟶ normalizedSyzygy S.X₃ := kernel.lift ε (S.f ≫ r) hbr
  have hb : b ≫ kernel.ι ε = S.f ≫ r := kernel.lift_ι _ _ _
  refine ⟨a, b, ?_, ?_⟩
  · have hd : (l ≫ r - 𝟙 F) ≫ ε = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, hr, hl, Category.id_comp, sub_self]
    let v : F ⟶ normalizedSyzygy S.X₃ := kernel.lift ε (l ≫ r - 𝟙 F) hd
    apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
    refine ⟨F, inferInstance, kernel.ι ε, v, ?_⟩
    apply (cancel_mono (kernel.ι ε)).mp
    rw [Category.assoc, kernel.lift_ι, Preadditive.sub_comp, Category.assoc,
      hb, ← Category.assoc, ha, Category.assoc, Category.id_comp,
      Preadditive.comp_sub, Category.comp_id]
  · have hd : (r ≫ l - 𝟙 S.X₂) ≫ S.g = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, hl, hr, Category.id_comp, sub_self]
    let v : S.X₂ ⟶ S.X₁ := hS.exact.lift (r ≫ l - 𝟙 S.X₂) hd
    apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
    refine ⟨S.X₂, inferInstance, S.f, v, ?_⟩
    apply (cancel_mono S.f).mp
    rw [Category.assoc, hS.exact.lift_f, Preadditive.sub_comp, Category.assoc,
      ha, ← Category.assoc, hb, Category.assoc, Category.id_comp,
      Preadditive.comp_sub, Category.comp_id]

end PolycyclicRecognition

end

end OAI
