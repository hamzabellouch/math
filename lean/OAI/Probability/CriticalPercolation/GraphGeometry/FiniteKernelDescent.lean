import Mathlib
import OAI.Probability.CriticalPercolation.Classification.AlgebraicDescent

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

universe u v

lemma hom_finite_preimage_of_finite_kernel {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hk : (f.ker : Set G).Finite) (S : Set H) (hS : S.Finite) :
    (f ⁻¹' S).Finite := by
  let _ := hk.to_subtype
  have hfib : ∀ a : H, (f ⁻¹' {a}).Finite := by
    intro a
    by_cases ha : (f ⁻¹' {a}).Nonempty
    · obtain ⟨x,hx⟩ := ha
      change f x=a at hx
      rw [←hx]
      let _ := Finite.of_equiv _ (f.fiberEquivKer x).symm
      exact Set.toFinite _
    · rw [Set.not_nonempty_iff_eq_empty.mp ha]
      exact Set.finite_empty
  apply (hS.biUnion (fun a _ => hfib a)).subset
  exact fun x hx => Set.mem_iUnion₂.mpr ⟨f x,hx,rfl⟩

lemma hom_finite_composite_kernel {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K)
    (hf : (f.ker : Set G).Finite) (hg : (g.ker : Set H).Finite) :
    ((g.comp f).ker : Set G).Finite :=
  hom_finite_preimage_of_finite_kernel f hf g.ker hg

theorem AlgebraicDescent.of_finite_kernel {N : Type u} [Group N]
    (hN : AlgebraicDescent N) :
    ∀ {G : Type v} [Group G] (ρ : G →* N), Surjective ρ →
      (ρ.ker : Set G).Finite → AlgebraicDescent G := by
  induction hN with
  | @finite N _ _ =>
    intro G _ ρ _ hk
    let _ := hk.to_subtype
    let _ := ρ.finite_iff_finite_ker_range.mpr ⟨inferInstance,inferInstance⟩
    exact AlgebraicDescent.finite G
  | @cyclic N _ φ hφ hf =>
    intro G _ ρ hρ hk
    exact AlgebraicDescent.cyclic G (φ.comp ρ) (hφ.comp hρ)
      (hom_finite_composite_kernel ρ φ hk hf)
  | @plane N _ φ hφ lower ih =>
    intro G _ ρ hρ hk
    apply AlgebraicDescent.plane G (φ.comp ρ) (hφ.comp hρ)
    intro J hJ
    let f := ρ.domRestrict J
    have hf : f.range≤φ.ker := by
      rintro n ⟨j,rfl⟩
      exact hJ j.property
    apply ih f.range hf f.rangeRestrict f.rangeRestrict_surjective
    apply (hk.preimage Subtype.val_injective.injOn).subset
    intro j hj
    exact congrArg Subtype.val hj

lemma AlgebraicDescent.of_equiv {G : Type u} {H : Type v} [Group G] [Group H]
    (hH : AlgebraicDescent H) (e : G ≃* H) : AlgebraicDescent G := by
  apply hH.of_finite_kernel e.toMonoidHom e.surjective
  have he : (e.toMonoidHom.ker : Set G)={1} := by
    ext g
    change e g=1 ↔ g=1
    rw [←e.map_one,e.injective.eq_iff]
  rw [he]
  exact Set.finite_singleton _

end CriticalPercolation
end
end
end

end OAI
