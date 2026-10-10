import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionHomology

namespace OAI

/-! # The top homology injection for an infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2

def cyclicTopHomologyInjection {G : Type} [Group G]
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (P : ProjectiveResolution (trivialIntegral q.ker)) (A : Rep ℤ G) (d : ℕ)
    (hvanish : IsZero (groupHomology (Rep.res q.ker.subtype A) (d + 1))) :
    groupHomology A (d + 1) ⟶ groupHomology (Rep.res q.ker.subtype A) d := by
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  exact (integerExtensionHomologyKernelIso q t ht P A d hvanish).hom ≫
    kernel.ι (HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) d) ≫
      (inducedResolutionHomologyIso q.ker A P d).hom

instance cyclicTopHomologyInjection_mono {G : Type} [Group G]
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (P : ProjectiveResolution (trivialIntegral q.ker)) (A : Rep ℤ G) (d : ℕ)
    (hvanish : IsZero (groupHomology (Rep.res q.ker.subtype A) (d + 1))) :
    Mono (cyclicTopHomologyInjection q t ht P A d hvanish) := by
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  apply (ModuleCat.mono_iff_injective _).mpr
  let E := integerExtensionHomologyKernelIso q t ht P A d hvanish
  let F := inducedResolutionHomologyIso q.ker A P d
  let k := kernel.ι (HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) d)
  have hE : Function.Injective E.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hF : Function.Injective F.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hk : Function.Injective k := (ModuleCat.mono_iff_injective _).mp inferInstance
  exact hF.comp (hk.comp hE)

theorem integralRankOne_properties_of_injective {M N : ModuleCat ℤ} (f : M ⟶ N)
    (hf : Function.Injective f)
    (htorsion : ∀ (z : ℤ) (x : N), z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : N, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) :
    (∀ (z : ℤ) (x : M), z • x = 0 → z = 0 ∨ x = 0) ∧
    (∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) := by
  constructor
  · intro z x hx
    have h := congrArg (fun x => f x) hx
    simp only [map_zsmul, map_zero] at h
    rcases htorsion z (f x) h with hz | hx
    · exact Or.inl hz
    · exact Or.inr (hf (hx.trans (map_zero f.hom).symm))
  · intro x y hx hy
    have hx' : f x ≠ 0 := fun h => hx (hf (h.trans (map_zero f.hom).symm))
    have hy' : f y ≠ 0 := fun h => hy (hf (h.trans (map_zero f.hom).symm))
    obtain ⟨a, b, ha, hb, h⟩ := hcomm _ _ hx' hy'
    refine ⟨a, b, ha, hb, hf ?_⟩
    simpa only [map_zsmul] using h

end PolycyclicRecognition

end

end OAI
