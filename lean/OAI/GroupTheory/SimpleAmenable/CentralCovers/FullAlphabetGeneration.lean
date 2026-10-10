import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallFamilyWords
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.EvaluationTable
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallFamilyGlobal

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FullAlphabetGeneration
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem five_alphabet_generate (hα : 5 ≤ Fintype.card α) :
    (⨆ I : FiveAlphabet α, (subtypeAlternatingHom I.val).range) = ⊤ := by
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro s hs
  obtain ⟨I,hSI,hIU,hI⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ s.val.support) (by rw [hs.card_support]; omega : s.val.support.card ≤ 5)
    (by simpa using hα : 5 ≤ (Finset.univ : Finset α).card)
  apply le_iSup (fun I : FiveAlphabet α => (subtypeAlternatingHom I.val).range) ⟨I,hIU,hI⟩
  exact (subtypeAlternatingHom_mem_range I s).mpr hSI

theorem universal_five_alphabet_generate [Group.IsPerfect (alternatingGroup α)]
    (hα : 5 ≤ Fintype.card α) :
    (⨆ I : FiveAlphabet α, (universalMap (subtypeAlternatingHom I.val)).range) = ⊤ :=
  universal_generating_ranges (fun I : FiveAlphabet α => subtypeAlternatingHom I.val)
    (five_alphabet_generate hα)

end FullAlphabetGeneration

section FullPrimitiveSectors

variable {α ι Ω : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω]

theorem smallFamilyModel_surjective (U : ι → Set Ω)
    (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (hα : 5 ≤ Fintype.card α) : Function.Surjective (smallFamilyModel (α := α) U) := by
  intro g
  obtain ⟨w,_,hw⟩ := smallFamilyModel_complete U hsep Finset.univ (by simpa using hα) g
    (fun ω => Finset.subset_univ _)
  exact ⟨w,hw⟩

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem fullPrimitiveProjection (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) :
    (coverMap M (alternatingGenerator a r m hm)).comp
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)) =
    (actualPolygonTableHom (primitiveTests (a := a) (r := r) P)).comp
      (smallFamilyModel (actualTestMask (primitiveTests (a := a) (r := r) P))) := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  simpa only [MonoidHom.comp_apply,smallFamilyModel,smallFamilyEval_of] using
    DFunLike.congr_fun (B.smallPrimitiveInputs_projection hlarge P I i) s

noncomputable def fullPrimitiveTable (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    ActualLawfulTable (coverMap M (alternatingGenerator a r m hm))
      (actualPolygonTableHom (primitiveTests (a := a) (r := r) P)) :=
  evaluationTable _ (smallFamilyEval (B.smallPrimitiveInputs hlarge P))
    (smallFamilyModel _) (actualPolygonTableHom _) (actualPolygonTableHom_injective _)
    (B.fullPrimitiveProjection hlarge P)
    (smallFamilyModel_surjective _ (actualTestMask_separates _)
      (by simpa using (by omega : 5 ≤ m+1)))
    (B.fullPrimitiveFamily_central hlarge P h)

omit [Finite ι] in

theorem primitiveFamily_range_full (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (J : Finset (Fin (m+1))) (hJ : 5 ≤ J.card) (b : Fin (m+1)) (hb : b ∉ J) :
    (copyFamilyEval (B.primitiveFamily J b hb P)).range ≤
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  rw [copyFamilyEval_range]
  apply iSup_le
  intro i
  rw [MonoidHom.range_eq_map,← subalphabet_five_generate J hJ,Subgroup.map_iSup]
  apply iSup_le
  intro I
  rw [← MonoidHom.range_comp]
  rintro x ⟨t,rfl⟩
  let I' : FiveAlphabet (Fin (m+1)) := ⟨I.val,Finset.subset_univ _,I.property.2⟩
  refine ⟨FreeGroup.of ⟨I',i,t⟩,?_⟩
  rw [smallFamilyEval_of]
  exact (DFunLike.congr_fun (B.primitiveFamily_inclusion I.property.1 _ _ _ _ P i) t).symm

omit [Finite ι] in
theorem constant_range_full (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) :
    B.c.range ≤ (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  rw [MonoidHom.range_eq_map,← five_alphabet_generate (by simpa using (by omega : 5 ≤ m+1)),
    Subgroup.map_iSup]
  apply iSup_le
  intro I
  rw [← MonoidHom.range_comp]
  rintro x ⟨s,rfl⟩
  refine ⟨FreeGroup.of ⟨I,none,s⟩,?_⟩
  rw [smallFamilyEval_of]
  change B.initialAlphabet I.val 0 s = B.c (subtypeAlternatingHom I.val s)
  rw [B.initialAlphabet_zero]
  rfl

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

noncomputable def fullGeometricSector (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a) : UniversalExtension (alternatingGroup (Fin (m+1))) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.fullPrimitiveTable hlarge P h).sector
    (resolvedPolygonMask (primitiveTests (a := a) (r := r) P) V.val)

theorem fullGeometricSector_projection (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.fullGeometricSector hlarge P h V) =
      (conditionalAlternatingHom V).comp (universalProjection (alternatingGroup (Fin (m+1)))) := by
  rw [fullGeometricSector,ActualLawfulTable.sector_projection]
  congr 1
  ext s : 1
  exact actualPolygonTableHom_resolved _ V hV s

end InitialCoverSystem
end FullPrimitiveSectors

end SimpleAmenable
end
end

end OAI
