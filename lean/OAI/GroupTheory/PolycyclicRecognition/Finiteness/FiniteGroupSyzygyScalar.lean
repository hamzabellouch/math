import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteGroupRelativeInjective
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedIdentityClass
import Mathlib.Algebra.Category.ModuleCat.Projective

namespace OAI

/-! # Descending a stable scalar through an integral split syzygy sequence -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

instance normalizedFreeRepresentation_integral_projective (A : Rep.{0} ℤ G) :
    Module.Projective ℤ (normalizedFreeRepresentation A) := by
  change Module.Projective ℤ ({a : A // a ≠ 0} →₀ ℤ[G])
  infer_instance

instance normalizedSyzygy_integral_projective (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] : Module.Projective ℤ (normalizedSyzygy A) := by
  let F := forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ)
  let S := normalizedSyzygySequence A
  have hS := (normalizedSyzygySequence_shortExact A).map_of_exact F
  let : Projective ((S.map F).X₃) := by
    change Projective (ModuleCat.of ℤ A)
    infer_instance
  let : Projective ((S.map F).X₂) := by
    change Projective (ModuleCat.of ℤ (normalizedFreeRepresentation A))
    infer_instance
  let sp := hS.splittingOfProjective
  have : Projective ((S.map F).X₁) :=
    (show Retract ((S.map F).X₁) ((S.map F).X₂) from
      ⟨(S.map F).f, sp.r, sp.f_r⟩).projective
  exact ModuleCat.projective_of_module_projective ((S.map F).X₁)

instance iteratedNormalizedSyzygy_integral_projective (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] (n : ℕ) :
    Module.Projective ℤ ((iteratedNormalizedSyzygy n).obj A) := by
  induction n with
  | zero => exact inferInstanceAs (Module.Projective ℤ A)
  | succ n ih =>
    let := ih
    change Module.Projective ℤ (normalizedSyzygy ((iteratedNormalizedSyzygy n).obj A))
    infer_instance

variable [Fintype G]

theorem stableScalar_descend (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    [Projective S.X₂] [Module.Projective ℤ S.X₃] (m : ℤ)
    (h : stableRepresentationClass S.X₁ S.X₁ (m • 𝟙 S.X₁) = 0) :
    stableRepresentationClass S.X₃ S.X₃ (m • 𝟙 S.X₃) = 0 := by
  let F := forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ)
  let : Projective ((S.map F).X₃) := by
    change Projective (ModuleCat.of ℤ S.X₃)
    infer_instance
  let sp := (hS.map_of_exact F).splittingOfProjective
  obtain ⟨P, hP, u, v, huv⟩ :=
    (stableRepresentationClass_eq_zero_iff_projective_factor _).mp h
  let := hP
  obtain ⟨l, hl⟩ := projective_extend_of_integral_retraction S.f sp.r.hom
    (fun a => ConcreteCategory.congr_hom sp.f_r a) P u
  let k : S.X₂ ⟶ S.X₂ := m • 𝟙 S.X₂ - l ≫ v ≫ S.f
  have hf : S.f ≫ (l ≫ v ≫ S.f) = m • S.f := by
    rw [← Category.assoc S.f l, hl, ← Category.assoc u v, huv,
      Preadditive.zsmul_comp, Category.id_comp]
  have hk : S.f ≫ k = 0 := by
    change S.f ≫ (m • 𝟙 S.X₂ - l ≫ v ≫ S.f) = 0
    rw [Preadditive.comp_sub, Preadditive.comp_zsmul, Category.comp_id, hf, sub_self]
  let := hS.epi_g
  let t := hS.exact.desc k hk
  have ht : S.g ≫ t = k := hS.exact.g_desc k hk
  apply (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
  refine ⟨S.X₂, inferInstance, t, S.g, ?_⟩
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, ht]
  have hg : (l ≫ v ≫ S.f) ≫ S.g = 0 := by
    rw [Category.assoc, Category.assoc, S.zero, comp_zero, comp_zero]
  change (m • 𝟙 S.X₂ - l ≫ v ≫ S.f) ≫ S.g = S.g ≫ (m • 𝟙 S.X₃)
  rw [Preadditive.sub_comp, Preadditive.zsmul_comp, Category.id_comp,
    hg, sub_zero, Preadditive.comp_zsmul, Category.comp_id]

theorem normalizedStableScalar_descend (A : Rep.{0} ℤ G) [Module.Projective ℤ A]
    (n : ℕ) (m : ℤ)
    (h : stableRepresentationClass ((iteratedNormalizedSyzygy n).obj A)
      ((iteratedNormalizedSyzygy n).obj A) (m • 𝟙 _) = 0) :
    stableRepresentationClass A A (m • 𝟙 A) = 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply ih
    let : Projective (normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj A)).X₂ := by
      change Projective (normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A))
      infer_instance
    let : Module.Projective ℤ (normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj A)).X₃ := by
      change Module.Projective ℤ ((iteratedNormalizedSyzygy n).obj A)
      infer_instance
    exact stableScalar_descend (normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj A))
      (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj A)) m h

end PolycyclicRecognition

end

end OAI
