import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.StarProjection
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry
import OAI.GroupTheory.SimpleAmenable.Configurations.FormalSectorProjection
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalLaws

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrimitiveFormalSectors
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι κ : Type*} [Finite ι] [Finite κ]

omit [Finite ι] in
theorem starFamily_projection (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (i : Option ι) :
    (coverMap M (alternatingGenerator a r m hm)).comp (A.starFamily hlarge P i)=
      (conditionalAlternatingHom (match i with
        | none => wholePolygon a
        | some i => primitiveTests (a := a) (r := r) P i)).comp (universalProjection _) := by
  cases i with
  | none => exact congrArg (fun f => f.comp (universalProjection _)) B.c_projection
  | some i =>
    apply B.fullGeometricSector_projection
    have he : spatialTranslate (P i).2 (initialTest a r (P i).1)=
        primitiveTests (a := a) (r := r)
          (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) (P i).2) (Sum.inl (P i).1) := by
      simp [primitiveTests,primitiveFamilyTests,translatedTemplate,initialPatchPrimitives]
    rw [he]
    exact resolved_test _ _

theorem formalSector_projection (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (T : FormalStarTable (A.starFamily hlarge P))
    (V : Set (ι → Bool)) (s : TrackStar (Fin (m+1))) :
    coverMap M (alternatingGenerator a r m hm) (T.sector V s)=
      formalPolygonTable (primitiveTests (a := a) (r := r) P)
        (sectorMask V (universalProjection _ s)) := by
  apply T.sector_projection (by simp only [Nat.card_fin]; omega)
    (coverMap M (alternatingGenerator a r m hm)) (actualPolygonTableHom _)
    (actualPolygonTableHom_injective _)
    (assignmentPullback (fun σ : Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) => σ.val))
    (assignmentPullback_surjective _ Subtype.val_injective)
  intro i
  rw [A.starFamily_projection]
  ext t : 1
  cases i with
  | none => exact (formalPolygonTable_whole _ _).symm
  | some i => exact (formalPolygonTable_test (primitiveTests (a := a) (r := r) P) i (universalProjection _ t)).symm

theorem formalSector_subfamily_eq (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (T : FormalStarTable (A.starFamily hlarge P)) (v : κ → ι)
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (U : Set (κ → Bool)) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (P ∘ v) i).val) V.val)
    (hUV : ∀ x, polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v)) x ∈ U ↔ x ∈ V.val) :
    T.sector ((fun σ : ι → Bool => σ ∘ v) ⁻¹' U)=
      B.fullGeometricSector hlarge (P ∘ v) h V := by
  apply (B.fullPrimitiveFamily_central hlarge (P ∘ v) h).lift_unique
    (coverMap M (alternatingGenerator a r m hm))
    (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).range
  · have hh := T.sector_subfamily_range v U
    have he : (fun i : Option κ => A.starFamily hlarge P (i.map v))=
        A.starFamily hlarge (P ∘ v) := by
      funext i; cases i <;> rfl
    rw [he,star_small_range_eq (by simpa using (by omega : 5 ≤ m+1)) _ _
      (A.starFamily_small hlarge (P ∘ v))] at hh
    exact hh
  · rintro x ⟨s,rfl⟩
    exact (B.fullPrimitiveTable hlarge (P ∘ v) h).sector_mem _ s
  · rw [B.fullGeometricSector_projection hlarge (P ∘ v) h V hV]
    apply MonoidHom.ext
    intro s
    rw [MonoidHom.comp_apply,A.formalSector_projection]
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro p
    change (actualPolygonTableHom _ _).val.val p = _
    rw [actualPolygonTableHom_apply]
    change ((sectorMask ((fun σ : ι → Bool => σ ∘ v) ⁻¹' U) (universalProjection _ s)
      (polygonAssignment (primitiveTests (a := a) (r := r) P) p.2)).val p.1,p.2)=
      conditionalPerm V (universalProjection _ s).val p
    rw [conditionalPerm_apply]
    have he : polygonAssignment (primitiveTests (a := a) (r := r) P) p.2 ∘ v=
        polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v)) p.2 := rfl
    have hp : polygonAssignment (primitiveTests (a := a) (r := r) P) p.2 ∈
        ((fun σ : ι → Bool => σ ∘ v) ⁻¹' U) ↔ p.2 ∈ V.val := by
      change _ ∘ v ∈ U ↔ _
      rw [he]
      exact hUV p.2
    by_cases hx : p.2 ∈ V.val
    · rw [sectorMask_of_mem _ _ _ (hp.mpr hx),ite_eq_left hx]
    · rw [sectorMask_of_not_mem _ _ _ (fun h => hx (hp.mp h)),ite_eq_right hx]
      rfl

end InitialCoverSystem.PatchAtlas
end PrimitiveFormalSectors

section FormalRectangleSplits

theorem resolvedPartitionSelector {a : ℕ} {ι D : Type*} [Nonempty D]
    (R : ι → polygonAlgebra a) (W : D → polygonAlgebra a)
    (hW : ∀ d, ResolvedBy (fun i => (R i).val) (W d).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val) :
    ∃ χ : (ι → Bool) → D, ∀ x d, χ (polygonAssignment R x)=d ↔ x ∈ (W d).val := by
  classical
  let C (σ : ι → Bool) (d : D) := ∃ x, polygonAssignment R x=σ ∧ x ∈ (W d).val
  let χ (σ : ι → Bool) : D := if h : ∃ d, C σ d then h.choose else Classical.choice inferInstance
  refine ⟨χ,?_⟩
  intro x d
  have hc : ∃ d, C (polygonAssignment R x) d := by
    obtain ⟨e,he⟩ := hcover x
    exact ⟨e,x,rfl,he⟩
  have hm : x ∈ (W (χ (polygonAssignment R x))).val := by
    have hh : C (polygonAssignment R x) (χ (polygonAssignment R x)) := by
      dsimp only [χ]
      rw [dite_eq_left hc]
      exact hc.choose_spec
    obtain ⟨y,hy,hm⟩ := hh
    exact (hW _ y x ((polygonAssignment_eq_iff R y x).mp hy)).mp hm
  constructor
  · intro he
    rwa [← he]
  · intro hd
    by_contra he
    exact Set.disjoint_left.mp (hdisjoint he) hm hd

namespace FormalStarTable
variable {α ι κ H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)] {F : Option ι → TrackStar α →* H}
    (T : FormalStarTable F)

theorem sector_empty : T.sector ∅=1 := by
  ext s
  change (centralSector T.model ∅ s).val=1
  rw [centralSector_empty]
  rfl

theorem sector_range_le_biUnion (W : κ → Set (ι → Bool)) (S : Finset κ)
    (hd : Pairwise fun i j => Disjoint (W i) (W j)) (K : Subgroup H)
    (hK : ∀ i ∈ S, (T.sector (W i)).range ≤ K) :
    (T.sector (⋃ i ∈ S, W i)).range ≤ K := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [T.sector_empty]
  | @insert i S hi ih =>
    have hdis : Disjoint (W i) (⋃ j ∈ S, W j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact hd (by intro he; subst j; exact hi hj)
    have he : (⋃ j ∈ insert i S, W j)=W i ∪ ⋃ j ∈ S, W j := by
      ext x
      simp only [Set.mem_iUnion,Finset.mem_insert,Set.mem_union]
      constructor
      · rintro ⟨j,(rfl|hj),hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨j,hj,hx⟩
      · rintro (hx|⟨j,hj,hx⟩)
        · exact ⟨i,Or.inl rfl,hx⟩
        · exact ⟨j,Or.inr hj,hx⟩
    rw [he]
    rintro x ⟨s,rfl⟩
    rw [T.sector_union hdis]
    exact K.mul_mem (hK i (Finset.mem_insert_self i S) ⟨s,rfl⟩)
      (ih (fun j hj => hK j (Finset.mem_insert_of_mem hj)) ⟨s,rfl⟩)

theorem sector_range_le_partition [Fintype κ] (W : κ → Set (ι → Bool)) (V : Set (ι → Bool))
    (hd : Pairwise fun i j => Disjoint (W i) (W j))
    (hc : ∀ σ, σ ∈ V ↔ ∃ i, σ ∈ W i) :
    (T.sector V).range ≤ ⨆ i, (T.sector (W i)).range := by
  have he : V=⋃ i ∈ (Finset.univ : Finset κ), W i := by
    ext σ
    simpa only [Set.mem_iUnion,Finset.mem_univ,exists_true_left] using hc σ
  rw [he]
  exact T.sector_range_le_biUnion W Finset.univ hd _ (fun i _ => le_iSup (fun j => (T.sector (W j)).range) i)

end FormalStarTable
end FormalRectangleSplits

end SimpleAmenable
end
end

end OAI
