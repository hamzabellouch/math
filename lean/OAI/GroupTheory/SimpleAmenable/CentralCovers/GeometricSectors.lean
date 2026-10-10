import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ResolvedBoolean

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GeometricSectors

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {ι : Type*} [Finite ι]

theorem actualPolygonTableHom_resolved (U : ι → polygonAlgebra a)
    (V : polygonAlgebra a) (hV : ResolvedBy (fun i => (U i).val) V.val)
    (s : alternatingGroup (Fin (m+1))) :
    actualPolygonTableHom U (sectorMask (resolvedPolygonMask U V.val) s) =
      conditionalAlternatingHom V s := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [actualPolygonTableHom_apply]
  change ((sectorMask (resolvedPolygonMask U V.val) s
      ⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩).val p.1,p.2) = conditionalPerm V s.val p
  rw [conditionalPerm_apply]
  by_cases hp : p.2 ∈ V.val
  · rw [sectorMask_of_mem _ _ _ ((resolvedPolygonMask_mem U V.val hV p.2).mpr hp),ite_eq_left hp]
  · rw [sectorMask_of_not_mem _ _ _ (fun h => hp ((resolvedPolygonMask_mem U V.val hV p.2).mp h)),ite_eq_right hp]
    rfl

theorem actualAlphabetTableHom_resolved (I : Finset (Fin (m+1)))
    (U : ι → polygonAlgebra a) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (U i).val) V.val) :
    (actualAlphabetTableHom I U).comp (sectorMask (resolvedPolygonMask U V.val)) =
      (conditionalAlternatingHom V).comp (subtypeAlternatingHom I) := by
  apply MonoidHom.ext
  intro s
  change actualPolygonTableHom U (tableAlphabetHom I (sectorMask _ s)) = _
  rw [tableAlphabetHom_mask]
  exact actualPolygonTableHom_resolved U V hV (subtypeAlternatingHom I s)

namespace InitialCoverSystem

variable (B : InitialCoverSystem a r m hm M)

noncomputable def geometricSector (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup I) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.primitiveTable I b hb P h).sector (resolvedPolygonMask (primitiveTests (r := r) P) V.val)

theorem geometricSector_projection (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.geometricSector I b hb P h V) =
      ((conditionalAlternatingHom V).comp (subtypeAlternatingHom I)).comp
        (universalProjection (alternatingGroup I)) := by
  unfold geometricSector
  rw [ActualLawfulTable.sector_projection,actualAlphabetTableHom_resolved I _ V hV]

theorem geometricSector_mem (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup I)) :
    B.geometricSector I b hb P h V s ∈ (copyFamilyEval (B.primitiveFamily I b hb P)).range :=
  (B.primitiveTable I b hb P h).sector_mem _ s

theorem geometricSector_aligned (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup I)) :
    B.geometricSector I b hb P h V s ∈ sourceAlignedGroup a r m hm M B.t I :=
  B.primitiveFamily_aligned I b hb P (B.geometricSector_mem I b hb P h V s)

theorem geometricSector_commute (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hd : Disjoint V.val W.val) (s t : UniversalExtension (alternatingGroup I)) :
    Commute (B.geometricSector I b hb P h V s) (B.geometricSector I b hb P h W t) :=
  (B.primitiveTable I b hb P h).sector_commute (resolvedPolygonMask_disjoint _ hV hd) s t

theorem geometricSector_union (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hd : Disjoint V.val W.val) (s : UniversalExtension (alternatingGroup I)) :
    B.geometricSector I b hb P h (V ⊔ W) s =
      B.geometricSector I b hb P h V s * B.geometricSector I b hb P h W s := by
  unfold geometricSector
  change (B.primitiveTable I b hb P h).sector (resolvedPolygonMask _ (V.val ∪ W.val)) s = _
  rw [resolvedPolygonMask_union]
  exact DFunLike.congr_fun ((B.primitiveTable I b hb P h).sector_union
    (resolvedPolygonMask_disjoint _ hV hd)) s

omit [Finite ι] in

theorem primitiveFamily_range_reindex {κ : Type*} (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) (v : κ → ι) :
    (copyFamilyEval (B.primitiveFamily I b hb (P ∘ v))).range ≤
      (copyFamilyEval (B.primitiveFamily I b hb P)).range := by
  rw [copyFamilyEval_range,copyFamilyEval_range]
  apply iSup_le
  intro i
  cases i with
  | none => exact le_iSup (fun z => (B.primitiveFamily I b hb P z).range) none
  | some j => exact le_iSup (fun z => (B.primitiveFamily I b hb P z).range) (some (v j))

theorem geometricSector_reindex {κ : Type*} [Finite κ] (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) (v : κ → ι)
    (h : B.PrimitiveFamilyLaw I b hb P) (g : B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (P ∘ v) i).val) V.val) :
    B.geometricSector I b hb (P ∘ v) g V = B.geometricSector I b hb P h V := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb P)).range h
  · rintro x ⟨s,rfl⟩
    exact B.primitiveFamily_range_reindex I b hb P v
      (B.geometricSector_mem I b hb (P ∘ v) g V s)
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb P h V s
  · have hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val := by
      intro x y he
      exact hV x y (fun j => he (v j))
    rw [B.geometricSector_projection I b hb (P ∘ v) g V hV,
      B.geometricSector_projection I b hb P h V hV']

end InitialCoverSystem
end GeometricSectors

end SimpleAmenable
end
end

end OAI
