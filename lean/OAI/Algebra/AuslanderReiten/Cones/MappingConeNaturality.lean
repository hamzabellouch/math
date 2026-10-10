import OAI.Algebra.AuslanderReiten.Homology.ShortExactTriangle
import OAI.Algebra.AuslanderReiten.Homology.CochainNullhomotopy

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit
open CompleteComparison

universe u
variable {R : Type u} [Ring R]
variable {F₁ G₁ F₂ G₂ : CochainComplex (ModuleCat.{u} R) ℤ}
variable {φ₁ : F₁ ⟶ G₁} {φ₂ : F₂ ⟶ G₂} {a : F₁ ⟶ F₂} {b : G₁ ⟶ G₂}
variable (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂)) (hH : H.hom 1 0 = 0)

include hH in

theorem mappingCone_map_snd_zero :
    (mappingCone.mapOfHomotopy H).f 0 ≫ (mappingCone.snd φ₂).v 0 0 (add_zero 0) =
      (mappingCone.snd φ₁).v 0 0 (add_zero 0) ≫ b.f 0 := by
  apply mappingCone.ext_from φ₁ 1 0 (by decide)
  · simp only [mappingCone.mapOfHomotopy, mappingCone.inl_v_desc_f_assoc,
      Cochain.add_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.comp_zero_cochain_v, Preadditive.add_comp, Category.assoc,
      mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v, Category.comp_id,
      Limits.comp_zero, mappingCone.inl_v_snd_v_assoc, Limits.zero_comp, zero_add]
    change H.hom 1 0 = 0
    exact hH
  · simp [mappingCone.mapOfHomotopy]

variable {L₁ L₂ : Type u} [AddCommGroup L₁] [Module R L₁]
  [AddCommGroup L₂] [Module R L₂]
variable (p₁ : CochainCokernel G₁ →ₗ[R] L₁) (p₂ : CochainCokernel G₂ →ₗ[R] L₂)
variable (hex₁ : Function.Exact (cochainCokernelMap φ₁) p₁)
  (hex₂ : Function.Exact (cochainCokernelMap φ₂) p₂)
variable (c : L₁ →ₗ[R] L₂)

include hH in

theorem rawConeQuotient_natural
    (hc : p₂.comp (cochainCokernelMap b) = c.comp p₁) :
    (rawConeQuotient φ₂ p₂ hex₂).comp (cochainCokernelMap (mappingCone.mapOfHomotopy H)) =
      c.comp (rawConeQuotient φ₁ p₁ hex₁) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range ((mappingCone φ₁).d (-1) 0).hom).mkQ_surjective x
  change p₂ (Submodule.Quotient.mk
    (((mappingCone.snd φ₂).v 0 0 (add_zero 0)).hom (((mappingCone.mapOfHomotopy H).f 0).hom x))) =
      c (p₁ (Submodule.Quotient.mk (((mappingCone.snd φ₁).v 0 0 (add_zero 0)).hom x)))
  have hs := congrArg (fun f : (mappingCone φ₁).X 0 ⟶ G₂.X 0 => f.hom x)
    (mappingCone_map_snd_zero H hH)
  change ((mappingCone.snd φ₂).v 0 0 (add_zero 0)).hom
      (((mappingCone.mapOfHomotopy H).f 0).hom x) =
    (b.f 0).hom (((mappingCone.snd φ₁).v 0 0 (add_zero 0)).hom x) at hs
  rw [hs]
  exact DFunLike.congr_fun hc (Submodule.Quotient.mk
    (((mappingCone.snd φ₁).v 0 0 (add_zero 0)).hom x))

end ArExplicit

end

end OAI
