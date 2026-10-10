import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.DiffuseSubfactor

namespace OAI

/-! Bounded Hochschild primitives on diffuse finite factors, with and without separable predual. -/

noncomputable section

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem primitive_of_separable_normal_factor
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  exact primitive_of_separable_normal_finite_paths e τ h1 htr hfaith
    (HochschildSakai.mul_hasPreadjoint e) (HochschildSakai.mul_right_hasPreadjoint e)
    hτ (HochschildUltrapower.finitePathTests_of_factor e τ hτ h1 htr hfaith hfactor hdiff)
    f hf hnormal

theorem primitive_of_separable_factor
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖ ≤ 12*‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  let F := reducedNormalCocycle e f
  let h := normalCorrection e f
  obtain ⟨g,hg,hgf⟩ := primitive_of_separable_normal_factor e τ hτ h1 htr hfaith
    hfactor hdiff F (reducedNormalCocycle_cocycle e f hf) (reducedNormalCocycle_normal e f)
  refine ⟨g+h,?_,?_⟩
  · have hF := reducedNormalCocycle_norm e f
    have hh := normalCorrection_norm e f
    exact (norm_add_le _ _).trans (by dsimp [F,h] at *; linarith)
  · intro x
    rw [differentialValue_add,hgf]
    exact (normal_correction_identity e f hf x).symm

end BoundedHochschild

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem primitive_of_normal_factor
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  classical
  let hL := HochschildSakai.mul_hasPreadjoint e
  let hR := HochschildSakai.mul_right_hasPreadjoint e
  obtain ⟨P,_hPn,hP⟩ := HochschildSakai.exists_abstract_star_preadjoint e
  apply primitive_of_finite_exactness e hL hR f ‖f‖ (norm_nonneg _)
  intro E
  let images : Finset M := Finset.univ.image (fun x : Fin (n+1) → E => f (fun i => x i))
  let D : Set M := (E : Set M) ∪ (images : Set M)
  have hD : D.Countable := E.countable_toSet.union images.countable_toSet
  obtain ⟨S,hS,hDS,hfactorN,hdiffN⟩ := HochschildLocalization.exists_countably_generated_diffuse_subfactor
    e τ hL hR P hP hτ h1 htr hfaith hfactor hdiff D hD
  let A := StarAlgebra.adjoin ℂ S
  let N := WeakAlgebra.closure e A hL hR P hP
  let Y := X ⧸ WeakSubspace.preannihilator (WeakAlgebra.linearClosure e A)
  let eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N := WeakAlgebra.predualEquiv e A hL hR P hP
  let τN : N →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ A hL hR P hP
  let : TopologicalSpace.SeparableSpace A := separable_starAdjoin S hS
  let : TopologicalSpace.SeparableSpace Y :=
    WeakAlgebra.separablePredual_of_separable e τ A hL hR P hP hτ hfaith
  have h1N : τN 1=1 := h1
  have htrN : ∀ a b : N, τN (a*b)=τN (b*a) := fun a b => htr a.val b.val
  have hLN : ∀ a : N, HasPreadjoint eN (ContinuousLinearMap.mul ℂ N a) :=
    WeakAlgebra.inherited_left_normal e A hL hR P hP
  have hτN : TraceInPredual eN τN :=
    WeakAlgebra.inheritedTrace_normal e τ A hL hR P hP hτ
  have hfaithN : ∀ a : N, τN (star a*a)=0 → a=0 :=
    WeakAlgebra.inheritedTrace_faithful e τ A hL hR P hP hfaith
  have hmem (a : M) (ha : a ∈ D) : a ∈ N :=
    WeakAlgebra.mem_linearClosure e A (StarAlgebra.subset_adjoin ℂ S (hDS ha))
  have hpaths := HochschildUltrapower.finitePathTests_of_factor eN τN hτN h1N htrN hfaithN hfactorN hdiffN
  apply finite_exactness_of_separable_subalgebra e eN τ τN h1N htr htrN hL hLN
    hτ hτN hfaith hfaithN N.subtype (fun _ => rfl) hpaths
    f hf hnormal (E : Set M)
  · intro a ha
    exact ⟨⟨a,hmem a (Or.inl ha)⟩,rfl⟩
  · intro x hx
    have hm : f x ∈ images := by
      apply Finset.mem_image.mpr
      refine ⟨fun i => ⟨x i,hx i⟩,Finset.mem_univ _,?_⟩
      rfl
    exact ⟨⟨f x,hmem _ (Or.inr hm)⟩,rfl⟩

theorem primitive_of_factor
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖ ≤ 12*‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  let F := reducedNormalCocycle e f
  let h := normalCorrection e f
  obtain ⟨g,hg,hgf⟩ := primitive_of_normal_factor e τ hτ h1 htr hfaith
    hfactor hdiff F (reducedNormalCocycle_cocycle e f hf) (reducedNormalCocycle_normal e f)
  refine ⟨g+h,?_,?_⟩
  · have hF := reducedNormalCocycle_norm e f
    have hh := normalCorrection_norm e f
    exact (norm_add_le _ _).trans (by dsimp [F,h] at *; linarith)
  · intro x
    rw [differentialValue_add,hgf]
    exact (normal_correction_identity e f hf x).symm

end BoundedHochschild

end

end OAI
