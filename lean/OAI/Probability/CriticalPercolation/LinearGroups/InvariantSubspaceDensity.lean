import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.FullSpanAlternative
import OAI.Probability.CriticalPercolation.LinearGroups.BurnsideDensity

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Nontrivial V] [Group G]

lemma invariant_subspace_of_not_fullSpan (ρ : G →* (V ≃ₗ[K] V)) (hρ : ¬FullSpan ρ) :
    ∃ W : Submodule K V, W≠⊥ ∧ W≠⊤ ∧ ∀ g, W.map (ρ g).toLinearMap=W := by
  let σ : G →* End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  let A := Algebra.adjoin K ((MonoidHom.mrange σ) : Set (End K V))
  have hAspan : A.toSubmodule=Submodule.span K (Set.range (fun g => (ρ g).toLinearMap)) := by
    rw [Algebra.adjoin_eq_span,Submonoid.closure_eq]
    rfl
  have hA : A≠⊤ := by
    intro he
    apply hρ
    change Submodule.span K (Set.range (fun g => (ρ g).toLinearMap))=⊤
    rw [←hAspan,he]
    rfl
  have hns : ¬IsSimpleModule A V := by
    intro h
    exact hA (subalgebra_eq_top_of_simple A)
  have he : ∃ P : Submodule A V, P≠⊥ ∧ P≠⊤ := by
    by_contra hn
    push Not at hn
    have : IsSimpleOrder (Submodule A V) := IsSimpleOrder.of_forall_eq_top hn
    exact hns ⟨⟩
  obtain ⟨P,hP0,hP1⟩ := he
  let W := P.restrictScalars K
  have hρmem (g : G) : (ρ g).toLinearMap∈A :=
    Algebra.subset_adjoin (show σ g∈(MonoidHom.mrange σ) from ⟨g,rfl⟩)
  have hstable (g : G) {v : V} (hv : v∈W) : ρ g v∈W :=
    P.smul_mem ⟨(ρ g).toLinearMap,hρmem g⟩ hv
  refine ⟨W,?_,?_,?_⟩
  · intro hw
    apply hP0
    apply Submodule.restrictScalars_injective K A V
    simpa only [Submodule.restrictScalars_bot] using hw
  · intro hw
    apply hP1
    apply Submodule.restrictScalars_injective K A V
    simpa only [Submodule.restrictScalars_top] using hw
  · intro g
    ext v
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hstable g hx
    · intro hv
      refine ⟨ρ g⁻¹ v,hstable g⁻¹ hv,?_⟩
      simp only [map_inv,LinearEquiv.coe_coe,LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply]

end CriticalPercolation.LinearGrowth
end
end

end OAI
