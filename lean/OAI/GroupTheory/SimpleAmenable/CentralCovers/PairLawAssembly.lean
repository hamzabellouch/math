import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AssignmentGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PairLawAssembly
variable {G E ι : Type*} [Group G] [Group E]

noncomputable def assignmentRestriction {Ω : Type*} (F : Ω → Type*) [∀ ω, Group (F ω)]
    (U : Set Ω) : (∀ ω, F ω) →* (∀ ω, F ω) := by
  classical
  exact { toFun := fun s ω => if ω ∈ U then s ω else 1
          map_one' := by ext ω; simp
          map_mul' := by intro s t; ext ω; by_cases hu : ω ∈ U <;> simp [hu] }

@[simp] theorem assignmentRestriction_single {Ω : Type*} [DecidableEq Ω]
    (F : Ω → Type*) [∀ ω, Group (F ω)] (U : Set Ω) [DecidablePred (· ∈ U)]
    (ω : Ω) (s : F ω) :
    assignmentRestriction F U (Pi.mulSingle ω s) =
      if ω ∈ U then Pi.mulSingle ω s else 1 := by
  classical
  ext ν
  by_cases heq : ν = ω
  · subst ν
    by_cases hu : ω ∈ U <;> simp [assignmentRestriction, hu]
  · by_cases huω : ω ∈ U <;> by_cases huν : ν ∈ U <;>
      simp [assignmentRestriction, heq, huω, huν]

variable [Fintype ι]
variable (A B : ι → Subgroup G) (h : ∀ i, CommutingFactors (A i) (B i))
    (hz : Subgroup.center G = ⊥)

noncomputable def refinementEquiv : (∀ σ : ι → Bool, refinedFactor A B Finset.univ σ) ≃* G := by
  classical
  exact commutingFactorsEquiv (fun σ => refinedFactor A B Finset.univ σ)
    (fun _ _ hστ _ _ hx hy => refinedFactor_commute A B h hστ hx hy)
    (simultaneous_refinement A B h hz Finset.univ) hz

@[simp] theorem refinementEquiv_single [DecidableEq (ι → Bool)] (σ : ι → Bool)
    (x : refinedFactor A B Finset.univ σ) :
    refinementEquiv A B h hz (Pi.mulSingle σ x) = x := by
  classical
  exact commutingFactorsEquiv_single _ _ _ _ _ _

theorem refinement_projection (i : ι) :
    ((h i).projectLeft hz).comp (refinementEquiv A B h hz).toMonoidHom =
      (refinementEquiv A B h hz).toMonoidHom.comp
        (assignmentRestriction (fun σ : ι → Bool => refinedFactor A B Finset.univ σ)
          {σ | σ i = true}) := by
  classical
  apply MonoidHom.pi_ext
  intro σ s
  change (h i).projectLeft hz (refinementEquiv A B h hz (Pi.mulSingle σ s)) =
    refinementEquiv A B h hz
      (assignmentRestriction (fun σ : ι → Bool => refinedFactor A B Finset.univ σ)
        {σ | σ i = true} (Pi.mulSingle σ s))
  rw [refinementEquiv_single, assignmentRestriction_single]
  have hs := s.property
  simp only [refinedFactor, assignmentFactor, Subgroup.mem_iInf, Finset.mem_univ,
    forall_const] at hs
  specialize hs i
  by_cases hσ : σ i = true
  · simp only [Set.mem_ofPred_eq, hσ, ↓reduceIte, refinementEquiv_single] at hs ⊢
    exact (h i).projectLeft_fix hz hs
  · simp only [Set.mem_ofPred_eq, hσ, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [map_one]
    exact (h i).projectLeft_kill hz hs

noncomputable def refinementSource (c : E →* G) (σ : ι → Bool) :
    E →* refinedFactor A B Finset.univ σ :=
  (Pi.evalMonoidHom _ σ).comp ((refinementEquiv A B h hz).symm.toMonoidHom.comp c)

noncomputable def simultaneousAssignmentMap (c : E →* G) : ((ι → Bool) → E) →* G :=
  (refinementEquiv A B h hz).toMonoidHom.comp
    (MonoidHom.pi fun σ => (refinementSource A B h hz c σ).comp (Pi.evalMonoidHom _ σ))

@[simp] theorem simultaneousAssignmentMap_whole (c : E →* G) :
    (simultaneousAssignmentMap A B h hz c).comp (sectorMask Set.univ) = c := by
  ext s
  change refinementEquiv A B h hz
    (fun σ => refinementSource A B h hz c σ (sectorMask Set.univ s σ)) = c s
  simp only [sectorMask_of_mem _ _ _ (Set.mem_univ _)]
  exact (refinementEquiv A B h hz).apply_symm_apply (c s)

theorem simultaneousAssignmentMap_test (c : E →* G) (i : ι) :
    (simultaneousAssignmentMap A B h hz c).comp (sectorMask {σ | σ i = true}) =
      ((h i).projectLeft hz).comp c := by
  ext s
  have hp := DFunLike.congr_fun (refinement_projection A B h hz i)
    ((refinementEquiv A B h hz).symm (c s))
  change (h i).projectLeft hz
      (refinementEquiv A B h hz ((refinementEquiv A B h hz).symm (c s))) =
    refinementEquiv A B h hz
      (assignmentRestriction (fun σ : ι → Bool => refinedFactor A B Finset.univ σ)
        {σ | σ i = true} ((refinementEquiv A B h hz).symm (c s))) at hp
  rw [MulEquiv.apply_symm_apply] at hp
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hp]
  change refinementEquiv A B h hz _ = refinementEquiv A B h hz _
  apply (refinementEquiv A B h hz).congr_arg
  ext σ
  by_cases hσ : σ i = true
  · simp [refinementSource, sectorMask, assignmentRestriction, hσ]
  · simp [refinementSource, sectorMask, assignmentRestriction, hσ]

theorem range_comp_subset {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : Y →* Z) (g : X →* Y) : (f.comp g).range ≤ f.range := by
  rintro y ⟨x, rfl⟩
  exact ⟨g x, rfl⟩

theorem simultaneous_assignment_surjection (c : E →* G) (g : ι → E →* G)
    (hinput : ∀ i, g i = ((h i).projectLeft hz).comp c)
    (hgenerate : c.range ⊔ ⨆ i, (g i).range = ⊤) :
    ∃ φ : ((ι → Bool) → E) →* G,
      Function.Surjective φ ∧ φ.comp (sectorMask Set.univ) = c ∧
        ∀ i, φ.comp (sectorMask {σ | σ i = true}) = g i := by
  let φ := simultaneousAssignmentMap A B h hz c
  have hwhole : φ.comp (sectorMask Set.univ) = c :=
    simultaneousAssignmentMap_whole A B h hz c
  have htest : ∀ i, φ.comp (sectorMask {σ | σ i = true}) = g i := by
    intro i
    exact (simultaneousAssignmentMap_test A B h hz c i).trans (hinput i).symm
  refine ⟨φ, ?_, hwhole, htest⟩
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  calc
    ⊤ = c.range ⊔ ⨆ i, (g i).range := hgenerate.symm
    _ ≤ φ.range := sup_le ?_ (iSup_le fun i => ?_)
  · calc c.range = (φ.comp (sectorMask Set.univ)).range :=
            congrArg MonoidHom.range hwhole.symm
         _ ≤ φ.range := range_comp_subset φ _
  · calc (g _).range = (φ.comp (sectorMask {σ | σ _ = true})).range :=
            congrArg MonoidHom.range (htest _).symm
         _ ≤ φ.range := range_comp_subset φ _

end PairLawAssembly

end SimpleAmenable
end
end

end OAI
