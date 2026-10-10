import OAI.Analysis.CircleDomains.Uniformization.FiniteCompletionUniformization

namespace OAI

namespace CircleDomainRigidity
open Set Function
open FiniteTransfer

/-- Only the finite Jordan models, including their actual sphere chart
changes, are needed by the downstream construction. -/
def FiniteJordanModelUniformization : Prop :=
  ∀ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ),
    Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) →
    ∀ e : Sphere ≃ₜ Sphere, ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f (e '' openCompletedRegion H) V

lemma finiteCircleUniformization_jordanModels (hfinite : FiniteCircleUniformization) :
    FiniteJordanModelUniformization := by
  intro n H hd e
  obtain ⟨V,f,hV,_hb,_hc,hf⟩ :=
    uniformize_finite_completion_after_homeomorphism hfinite H hd (W := ∅) e
      (empty_subset _) (fun _ h => h.elim)
  exact ⟨V,f ∘ e.symm,hV,hf⟩

namespace FiniteTransfer

lemma uniformize_finite_completion_of_jordan_models
    (hmodels : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {W : Set Sphere} (e : Sphere ≃ₜ Sphere)
    (hW : W ⊆ openCompletedRegion H) (he : IsConformalOn e W) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ BijOn f (openCompletedRegion H) V ∧ IsConformalOn f W ∧
        IsConformalEquivalence (f ∘ e.symm) (e '' openCompletedRegion H) V := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let a : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let H' : Fin (Fintype.card I) → ℂ ≃ₜ ℂ := fun i => H (a.symm i)
  have hd' : Pairwise (Disjoint on fun i => closure (jordanInterior (H' i))) :=
    fun _ _ hij => hd (a.symm.injective.ne hij)
  have hreg : openCompletedRegion H'=openCompletedRegion H := by
    apply congrArg compl
    ext p
    constructor
    · intro hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨a.symm i,hi⟩
    · intro hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp hp
      apply mem_iUnion.mpr
      refine ⟨a i,?_⟩
      simpa only [H',a.symm_apply_apply] using hi
  obtain ⟨V,g,hV,hg⟩ := hmodels (Fintype.card I) H' hd' e
  rw [hreg] at hg
  refine ⟨V,g ∘ e,hV,hg.bijOn.comp e.injective.bijOn_image,
    hg.1.comp he (fun p hp => ⟨p,hW hp,rfl⟩),?_⟩
  have heq : (g ∘ e) ∘ e.symm=g := by funext p; simp only [comp_apply,e.apply_symm_apply]
  simpa only [heq] using hg

end FiniteTransfer
end CircleDomainRigidity

end OAI
