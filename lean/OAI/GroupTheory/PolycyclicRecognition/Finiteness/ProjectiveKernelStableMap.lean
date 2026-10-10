import OAI.GroupTheory.PolycyclicRecognition.Algebra.PresentationKernelMap

namespace OAI

/-! # Maps between projective presentations preserve stable zero maps -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem projectiveKernelMap_stable_zero
    {S T : ShortComplex (Rep.{0} ℤ G)} (_hS : S.ShortExact) (hT : T.ShortExact)
    [Projective S.X₂] (φ : S ⟶ T)
    (hφ : stableRepresentationClass _ _ φ.τ₃ = 0) :
    stableRepresentationClass _ _ φ.τ₁ = 0 := by
  let : Mono T.f := hT.mono_f
  let : Epi T.g := hT.epi_g
  obtain ⟨P, hP, u, v, huv⟩ := (stableRepresentationClass_eq_zero_iff_projective_factor _).mp hφ
  let : Projective P := hP
  let l : P ⟶ T.X₂ := Projective.factorThru v T.g
  have hl : l ≫ T.g = v := Projective.factorThru_comp _ _
  let d := φ.τ₂ - S.g ≫ u ≫ l
  have hd : d ≫ T.g = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, φ.comm₂₃, Category.assoc, Category.assoc, hl, huv, sub_self]
  let w := hT.exact.lift d hd
  apply (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
  refine ⟨S.X₂, inferInstance, S.f, w, ?_⟩
  apply (cancel_mono T.f).mp
  rw [Category.assoc, hT.exact.lift_f, φ.comm₁₂]
  dsimp only [d]
  rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc,
    S.zero, zero_comp, zero_comp, sub_zero]

def projectivePresentationMap
    (S T : ShortComplex (Rep.{0} ℤ G)) (_hS : S.ShortExact) (hT : T.ShortExact)
    [Projective S.X₂] (f : S.X₃ ⟶ T.X₃) : S ⟶ T := by
  let : Mono T.f := hT.mono_f
  let : Epi T.g := hT.epi_g
  let l := Projective.factorThru (S.g ≫ f) T.g
  have hl : l ≫ T.g = S.g ≫ f := Projective.factorThru_comp _ _
  have hk : (S.f ≫ l) ≫ T.g = 0 := by
    rw [Category.assoc, hl, ← Category.assoc, S.zero, zero_comp]
  exact { τ₁ := hT.exact.lift (S.f ≫ l) hk
          τ₂ := l
          τ₃ := f
          comm₁₂ := hT.exact.lift_f _ _
          comm₂₃ := hl }

@[simp]
theorem projectivePresentationMap_τ₃
    (S T : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) (hT : T.ShortExact)
    [Projective S.X₂] (f : S.X₃ ⟶ T.X₃) :
    (projectivePresentationMap S T hS hT f).τ₃ = f := rfl

theorem projectiveKernelMap_stable_eq
    {S T : ShortComplex (Rep.{0} ℤ G)} (hS : S.ShortExact) (hT : T.ShortExact)
    [Projective S.X₂] (φ ψ : S ⟶ T)
    (hφψ : stableRepresentationClass _ _ φ.τ₃ = stableRepresentationClass _ _ ψ.τ₃) :
    stableRepresentationClass _ _ φ.τ₁ = stableRepresentationClass _ _ ψ.τ₁ := by
  have h : stableRepresentationClass _ _ (φ - ψ).τ₃ = 0 := by
    rw [ShortComplex.sub_τ₃, map_sub, hφψ, sub_self]
  have hz := projectiveKernelMap_stable_zero hS hT (φ - ψ) h
  rw [ShortComplex.sub_τ₁, map_sub] at hz
  exact sub_eq_zero.mp hz

end PolycyclicRecognition

end

end OAI
