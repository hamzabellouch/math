import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Components
import OAI.RepresentationTheory.PartialPermutation.CentralKernels

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
noncomputable section
open scoped MonoidAlgebra BigOperators

section CompleteKernels
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

def componentRep (c : isotypicComponents ℂ[G] ρ.asModule) :=
  (Subrepresentation.ofSubmodule' (componentSimple ρ c)).toRepresentation

instance componentRep_irreducible (c : isotypicComponents ℂ[G] ρ.asModule) :
    Representation.IsIrreducible (componentRep ρ c) :=
  (subrep_irreducible_iff ρ _).mpr (componentSimple_simple ρ c)

lemma componentRep_equiv_iff (c d : isotypicComponents ℂ[G] ρ.asModule) :
    Nonempty (Representation.Equiv (componentRep ρ c) (componentRep ρ d)) ↔ c = d := by
  constructor
  · rintro ⟨e⟩
    apply componentCharacter_injective ρ
    exact Subtype.ext (Representation.char_iso e)
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

omit [FiniteDimensional ℂ V] in
lemma complexFourier_subrep (σ : Subrepresentation ρ) (a : G → ℂ) (x : σ) :
    ((complexFourier σ.toRepresentation a x : σ) : V) = complexFourier ρ a x := by
  simp only [complexFourier, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul]
  rfl

omit [FiniteDimensional ℂ V] in
lemma complexFourier_sum {ι : Type*} [Fintype ι] (a : ι → G → ℂ) :
    complexFourier ρ (fun g => ∑ i, a i g) = ∑ i, complexFourier ρ (a i) := by
  simp only [complexFourier, Finset.sum_smul]
  exact Finset.sum_comm

lemma sum_character_kernels_identity
    [Fintype (isotypicComponents ℂ[G] ρ.asModule)] :
    complexFourier ρ (fun g => ∑ c, centralCharacterKernel (componentRep ρ c) g) = 1 := by
  classical
  let K : G → ℂ := fun g => ∑ c, centralCharacterKernel (componentRep ρ c) g
  have hs (σ : Subrepresentation ρ) [Representation.IsIrreducible σ.toRepresentation] :
      complexFourier σ.toRepresentation K = 1 := by
    let χ : OccurringTypes ρ := ⟨σ.toRepresentation.character, σ, inferInstance, rfl⟩
    obtain ⟨c, hc⟩ := componentCharacter_surjective ρ χ
    have he : Nonempty (Representation.Equiv (componentRep ρ c) σ.toRepresentation) := by
      exact irreducible_equiv_of_character_eq σ.toRepresentation (componentRep ρ c)
        (congrArg Subtype.val hc).symm
    rw [complexFourier_sum]
    rw [Finset.sum_eq_single c]
    · rw [centralCharacterKernel_fourier, ite_eq_left he]
    · intro d _ hdc
      rw [centralCharacterKernel_fourier, ite_eq_right]
      rintro ⟨e⟩
      obtain ⟨ec⟩ := he
      exact hdc ((componentRep_equiv_iff ρ d c).mp ⟨e.trans ec.symm⟩)
    · simp
  let E (S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S}) : Submodule ℂ V :=
    S.val.restrictScalars ℂ
  have htop : (⨆ S, E S) = ⊤ := by
    change (⨆ S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S},
      S.val.restrictScalars ℂ) = ⊤
    rw [← Submodule.restrictScalars_iSup]
    have ht : (⨆ S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S}, S.val) = ⊤ :=
      (sSup_eq_iSup' {S : Submodule ℂ[G] ρ.asModule | IsSimpleModule ℂ[G] S}).symm.trans
        (IsSemisimpleModule.sSup_simples_eq_top ℂ[G] ρ.asModule)
    rw [ht, Submodule.restrictScalars_top]
  have hker : (⊤ : Submodule ℂ V) ≤ LinearMap.ker (complexFourier ρ K - 1) := by
    rw [← htop]
    refine iSup_le fun S => ?_
    intro x hx
    let σ := Subrepresentation.ofSubmodule' S.val
    have : Representation.IsIrreducible σ.toRepresentation :=
      (subrep_irreducible_iff ρ σ).mpr S.property
    have ht := congrArg (fun A : Module.End ℂ σ.toSubmodule => ((A ⟨x, hx⟩ : σ.toSubmodule) : V)) (hs σ)
    rw [complexFourier_subrep] at ht
    simpa using sub_eq_zero.mpr ht
  ext x
  have hx := hker (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ V))
  simpa [LinearMap.mem_ker, sub_eq_zero] using hx

end CompleteKernels
end
end PartialPermutation

end

end OAI
